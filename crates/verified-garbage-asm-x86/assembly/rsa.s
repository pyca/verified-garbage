// The functions of `src/rsa.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_recover_primes_det:
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], ebp
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov edi, eax
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
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
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov eax, 0
23:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 23b
	mov eax, 0
	jmp 21f
20:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov ecx, 0
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov eax, 0
24:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 24b
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
25:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 25b
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	add esi, ecx
	sub esi, 1
26:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 26b
	mov esi, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	add eax, edx
	sub eax, 12
	mov ecx, -2147483648
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+32]
	add esi, esi
	add esi, esi
	add esi, esi
28:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+104], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 29f
	jmp 210f
29:
211:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 211b
210:
	and edx, 15
	jne 212f
	jmp 213f
212:
214:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 214b
213:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
215:
	cmp edx, 32
	jae 216f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 217f
216:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
217:
	cmp edx, 0
	jne 215b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
218:
	cmp edx, 32
	jae 219f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 220f
219:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
220:
	cmp edx, 0
	jne 218b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
221:
	cmp edx, 32
	jae 222f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 223f
222:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
223:
	cmp edx, 0
	jne 221b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+108], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 224f
	jmp 225f
224:
226:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 226b
225:
	and edx, 15
	jne 227f
	jmp 228f
227:
229:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 229b
228:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
230:
	cmp edx, 32
	jae 231f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 232f
231:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
232:
	cmp edx, 0
	jne 230b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
233:
	cmp edx, 32
	jae 234f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 235f
234:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
235:
	cmp edx, 0
	jne 233b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
236:
	cmp edx, 32
	jae 237f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 238f
237:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
238:
	cmp edx, 0
	jne 236b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+108], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 239f
	jmp 240f
239:
241:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 241b
240:
	and edx, 15
	jne 242f
	jmp 243f
242:
244:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 244b
243:
	mov edi, DWORD PTR [esp+44]
	mov ebx, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
245:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 245b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	sub esi, 1
	cmp esi, 0
	jne 28b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
246:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 246b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
247:
	cmp edx, 32
	jae 248f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 249f
248:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
249:
	cmp edx, 0
	jne 247b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
250:
	cmp edx, 32
	jae 251f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 252f
251:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
252:
	cmp edx, 0
	jne 250b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+120], ebx
	mov eax, DWORD PTR [edi+116]
	or eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+144]
	xor eax, 1
	mov DWORD PTR [edi+144], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 253f
	jmp 254f
253:
255:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 255b
254:
	and edi, 15
	jne 256f
	jmp 257f
256:
258:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 258b
257:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, 0
259:
	cmp edx, 32
	jae 260f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 261f
260:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
261:
	cmp edx, 0
	jne 259b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 262f
	jmp 263f
262:
264:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 264b
263:
	and edi, 15
	jne 265f
	jmp 266f
265:
267:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 267b
266:
	mov edi, DWORD PTR [esp+44]
	mov eax, 512
	mov DWORD PTR [edi+120], eax
268:
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 8
	mov ecx, DWORD PTR [edi+120]
	cmp ecx, eax
	jb 269f
	jmp 270f
269:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, 0
	mov edx, DWORD PTR [edi+120]
271:
	or ecx, DWORD PTR [esi]
	or ecx, DWORD PTR [ebp]
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 271b
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	add ecx, 4
	mov eax, 0
272:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 272b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [edi+120]
	add esi, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, DWORD PTR [edi+120]
	sub edx, eax
273:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 273b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 274f
	jmp 275f
274:
276:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 276b
275:
	and edi, 15
	jne 277f
	jmp 278f
277:
279:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 279b
278:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	add ecx, 4
	mov eax, 0
280:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 280b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [edi+120]
	add esi, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, DWORD PTR [edi+120]
	sub edx, eax
281:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 281b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 282f
	jmp 283f
282:
284:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 284b
283:
	and edi, 15
	jne 285f
	jmp 286f
285:
287:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 287b
286:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
288:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 288b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [edi+120]
	add ebp, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov eax, DWORD PTR [edi+120]
	sub edx, eax
289:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 289b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 290f
	jmp 291f
290:
292:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 292b
291:
	and edi, 15
	jne 293f
	jmp 294f
293:
295:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 295b
294:
	mov edi, DWORD PTR [esp+44]
270:
	mov eax, DWORD PTR [edi+120]
	shr eax, 1
	mov DWORD PTR [edi+120], eax
	cmp eax, 4
	jae 268b
	mov eax, 16
	mov DWORD PTR [edi+128], eax
296:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [esi]
	or eax, DWORD PTR [ebp]
	mov ecx, eax
	mov edx, DWORD PTR [edi+128]
297:
	shr eax, 1
	sub edx, 1
	jne 297b
	mov edx, DWORD PTR [edi+128]
298:
	add eax, eax
	sub edx, 1
	jne 298b
	xor ecx, eax
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 299f
	jmp 2100f
299:
2101:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2101b
2100:
	and edi, 15
	jne 2102f
	jmp 2103f
2102:
2104:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2104b
2103:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+100], eax
2105:
	mov ebx, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
2106:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2106b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+100]
	sub eax, 1
	mov DWORD PTR [edi+100], eax
	jne 2105b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2107f
	jmp 2108f
2107:
2109:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2109b
2108:
	and edi, 15
	jne 2110f
	jmp 2111f
2110:
2112:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2112b
2111:
	mov edi, DWORD PTR [esp+44]
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2113f
	jmp 2114f
2113:
2115:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2115b
2114:
	and edi, 15
	jne 2116f
	jmp 2117f
2116:
2118:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2118b
2117:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+100], eax
2119:
	mov ebx, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
2120:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2120b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+100]
	sub eax, 1
	mov DWORD PTR [edi+100], eax
	jne 2119b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2121f
	jmp 2122f
2121:
2123:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2123b
2122:
	and edi, 15
	jne 2124f
	jmp 2125f
2124:
2126:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2126b
2125:
	mov edi, DWORD PTR [esp+44]
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2127f
	jmp 2128f
2127:
2129:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2129b
2128:
	and edi, 15
	jne 2130f
	jmp 2131f
2130:
2132:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2132b
2131:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+100], eax
2133:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2134:
	cmp edx, 32
	jae 2135f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2136f
2135:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2136:
	cmp edx, 0
	jne 2134b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+100]
	sub eax, 1
	mov DWORD PTR [edi+100], eax
	jne 2133b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2137f
	jmp 2138f
2137:
2139:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2139b
2138:
	and edi, 15
	jne 2140f
	jmp 2141f
2140:
2142:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2142b
2141:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	shr eax, 1
	mov DWORD PTR [edi+128], eax
	cmp eax, 1
	jae 296b
	mov eax, 512
	mov DWORD PTR [edi+120], eax
2143:
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 8
	mov ecx, DWORD PTR [edi+120]
	cmp ecx, eax
	jb 2144f
	jmp 2145f
2144:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, 0
	mov edx, DWORD PTR [edi+120]
2146:
	or ecx, DWORD PTR [esi]
	or ecx, DWORD PTR [ebp]
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2146b
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	add ecx, 4
	mov eax, 0
2147:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2147b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [edi+120]
	add esi, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, DWORD PTR [edi+120]
	sub edx, eax
2148:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2148b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2149f
	jmp 2150f
2149:
2151:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2151b
2150:
	and edi, 15
	jne 2152f
	jmp 2153f
2152:
2154:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2154b
2153:
	mov edi, DWORD PTR [esp+44]
2145:
	mov eax, DWORD PTR [edi+120]
	shr eax, 1
	mov DWORD PTR [edi+120], eax
	cmp eax, 4
	jae 2143b
	mov eax, 16
	mov DWORD PTR [edi+128], eax
2155:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [esi]
	or eax, DWORD PTR [ebp]
	mov ecx, eax
	mov edx, DWORD PTR [edi+128]
2156:
	shr eax, 1
	sub edx, 1
	jne 2156b
	mov edx, DWORD PTR [edi+128]
2157:
	add eax, eax
	sub edx, 1
	jne 2157b
	xor ecx, eax
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2158f
	jmp 2159f
2158:
2160:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2160b
2159:
	and edi, 15
	jne 2161f
	jmp 2162f
2161:
2163:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2163b
2162:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+100], eax
2164:
	mov ebx, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
2165:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2165b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+100]
	sub eax, 1
	mov DWORD PTR [edi+100], eax
	jne 2164b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2166f
	jmp 2167f
2166:
2168:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2168b
2167:
	and edi, 15
	jne 2169f
	jmp 2170f
2169:
2171:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2171b
2170:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	shr eax, 1
	mov DWORD PTR [edi+128], eax
	cmp eax, 1
	jae 2155b
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2172f
	jmp 2173f
2172:
2174:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2174b
2173:
	and edi, 15
	jne 2175f
	jmp 2176f
2175:
2177:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2177b
2176:
	mov edi, DWORD PTR [esp+44]
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2178f
	jmp 2179f
2178:
2180:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2180b
2179:
	and edi, 15
	jne 2181f
	jmp 2182f
2181:
2183:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2183b
2182:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	mov DWORD PTR [edi+52], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	mov DWORD PTR [edi+56], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	shr edx, 1
	mov DWORD PTR [edi+60], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+64], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+68], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+72], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+76], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+80], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+84], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+88], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	shr eax, 1
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 8
	add eax, 8
	mov DWORD PTR [edi+96], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2184:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2184b
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2185f
	jmp 2186f
2185:
2187:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2187b
2186:
	and edi, 15
	jne 2188f
	jmp 2189f
2188:
2190:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2190b
2189:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2191:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2191b
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2192f
	jmp 2193f
2192:
2194:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2194b
2193:
	and edi, 15
	jne 2195f
	jmp 2196f
2195:
2197:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2197b
2196:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2198:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2198b
	mov ecx, DWORD PTR [edi+160]
	and ecx, 1
	sub ecx, 1
	mov ebp, DWORD PTR [edi+76]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2199f
	jmp 2200f
2199:
2201:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2201b
2200:
	and edi, 15
	jne 2202f
	jmp 2203f
2202:
2204:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2204b
2203:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	add eax, 8
	mov edi, edi
	add edi, 160
	add eax, eax
	add eax, eax
	add eax, eax
	add edi, eax
	shr eax, 1
	shr eax, 1
	shr eax, 1
	mov ecx, 0
2205:
	cmp edx, 32
	jae 2206f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2207f
2206:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2207:
	cmp edx, 0
	jne 2205b
	mov edi, DWORD PTR [esp+44]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov ebp, DWORD PTR [edi+76]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
2208:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi], eax
	add ebp, 4
	add esi, 16
	sub ecx, 1
	jne 2208b
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
2209:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi+4], eax
	add ebp, 4
	add esi, 16
	sub ecx, 1
	jne 2209b
	mov eax, 1
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 8
	shr eax, 2
	mov ecx, eax
	add eax, ecx
	add eax, ecx
	add eax, 6
	shr eax, 1
	mov DWORD PTR [edi+100], eax
2210:
	mov ebx, DWORD PTR [edi+64]
	add ebx, 16
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+24], eax
	mov eax, 1
	mov DWORD PTR [edi+28], eax
	mov eax, 0
	mov DWORD PTR [edi+32], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov eax, 1
	mov DWORD PTR [edi+40], eax
	mov esi, 30
2211:
	sub esi, 1
	mov eax, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+16]
	mov ebx, edx
	and eax, 1
	mov ecx, 0
	sub ecx, eax
	shr edx, 31
	sub edx, 1
	and edx, ecx
	mov eax, ebx
	xor eax, edx
	sub eax, edx
	add eax, 2
	mov DWORD PTR [edi+16], eax
	mov ebx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [edi+24]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	shr eax, 1
	mov DWORD PTR [edi+20], ebx
	mov DWORD PTR [edi+24], eax
	mov ebx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+36]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+28], ebx
	mov DWORD PTR [edi+36], eax
	mov ebx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [edi+40]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+32], ebx
	mov DWORD PTR [edi+40], eax
	test esi, esi
	jne 2211b
	mov eax, DWORD PTR [edi+28]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+32]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+36]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+40]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+172], eax
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
2212:
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+8], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 2212b
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+28]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+32]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967288], ebx
	mov edi, DWORD PTR [esp+44]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
2213:
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967292], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+12], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 2213b
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967292], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+36]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+40]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967292], ebx
	mov edi, DWORD PTR [esp+44]
	mov ebx, DWORD PTR [edi+64]
	add ebx, 16
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+24], eax
	mov eax, 1
	mov DWORD PTR [edi+28], eax
	mov eax, 0
	mov DWORD PTR [edi+32], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov eax, 1
	mov DWORD PTR [edi+40], eax
	mov esi, 30
2214:
	sub esi, 1
	mov eax, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+16]
	mov ebx, edx
	and eax, 1
	mov ecx, 0
	sub ecx, eax
	shr edx, 31
	sub edx, 1
	and edx, ecx
	mov eax, ebx
	xor eax, edx
	sub eax, edx
	add eax, 2
	mov DWORD PTR [edi+16], eax
	mov ebx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [edi+24]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	shr eax, 1
	mov DWORD PTR [edi+20], ebx
	mov DWORD PTR [edi+24], eax
	mov ebx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+36]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+28], ebx
	mov DWORD PTR [edi+36], eax
	mov ebx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [edi+40]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+32], ebx
	mov DWORD PTR [edi+40], eax
	test esi, esi
	jne 2214b
	mov eax, DWORD PTR [edi+28]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+32]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+36]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+40]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+172], eax
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
2215:
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967280], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+24]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+28]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 2215b
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967280], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967288]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+28]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967292]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+32]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967280], ebx
	mov edi, DWORD PTR [esp+44]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
2216:
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967284], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+24]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+28]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 2216b
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967284], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967288]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+36]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967292]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+40]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967284], ebx
	mov edi, DWORD PTR [esp+44]
	mov esi, DWORD PTR [edi+100]
	sub esi, 1
	mov DWORD PTR [edi+100], esi
	test esi, esi
	jne 2210b
	mov ebx, DWORD PTR [edi+64]
	add ebx, 16
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+24], eax
	mov eax, 1
	mov DWORD PTR [edi+28], eax
	mov eax, 0
	mov DWORD PTR [edi+32], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov eax, 1
	mov DWORD PTR [edi+40], eax
	mov esi, 30
2217:
	sub esi, 1
	mov eax, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+16]
	mov ebx, edx
	and eax, 1
	mov ecx, 0
	sub ecx, eax
	shr edx, 31
	sub edx, 1
	and edx, ecx
	mov eax, ebx
	xor eax, edx
	sub eax, edx
	add eax, 2
	mov DWORD PTR [edi+16], eax
	mov ebx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [edi+24]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	shr eax, 1
	mov DWORD PTR [edi+20], ebx
	mov DWORD PTR [edi+24], eax
	mov ebx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+36]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+28], ebx
	mov DWORD PTR [edi+36], eax
	mov ebx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [edi+40]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+32], ebx
	mov DWORD PTR [edi+40], eax
	test esi, esi
	jne 2217b
	mov eax, DWORD PTR [edi+28]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+32]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+36]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+40]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+172], eax
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
2218:
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+8], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 2218b
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+28]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+32]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967288], ebx
	mov edi, DWORD PTR [esp+44]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
2219:
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967292], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+12], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 2219b
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967292], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+36]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+40]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967292], ebx
	mov edi, DWORD PTR [esp+44]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov ebp, DWORD PTR [edi+92]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
2220:
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp], eax
	add ebp, 4
	add esi, 16
	sub ecx, 1
	jne 2220b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2221:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2221b
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2222:
	cmp edx, 32
	jae 2223f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2224f
2223:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2224:
	cmp edx, 0
	jne 2222b
	mov edi, DWORD PTR [esp+44]
	mov ebx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	xor ecx, -1
	mov ebp, DWORD PTR [edi+92]
	mov ebx, DWORD PTR [edi+84]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2225f
	jmp 2226f
2225:
2227:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2227b
2226:
	and edi, 15
	jne 2228f
	jmp 2229f
2228:
2230:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2230b
2229:
	mov edi, DWORD PTR [esp+44]
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2231f
	jmp 2232f
2231:
2233:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2233b
2232:
	and edi, 15
	jne 2234f
	jmp 2235f
2234:
2236:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2236b
2235:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	add ecx, 4
	mov eax, 0
2237:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2237b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2238:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2238b
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2239f
	jmp 2240f
2239:
2241:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2241b
2240:
	and edi, 15
	jne 2242f
	jmp 2243f
2242:
2244:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2244b
2243:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2245:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2245b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2246:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2246b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
2247:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+96]
	add eax, eax
	add eax, eax
	add ebx, eax
	mov ecx, DWORD PTR [ebx]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add ebp, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov ebx, 0
2248:
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2248b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	shr ecx, 2
	cmp eax, ecx
	jne 2247b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2249:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2249b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add eax, ecx
	mov ecx, 0
	mov DWORD PTR [eax], ecx
	mov DWORD PTR [eax+4], ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2250:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2250b
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2251f
	jmp 2252f
2251:
2253:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2253b
2252:
	and edi, 15
	jne 2254f
	jmp 2255f
2254:
2256:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2256b
2255:
	mov edi, DWORD PTR [esp+44]
	mov eax, 0
	mov DWORD PTR [edi+104], eax
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 4
	mov eax, DWORD PTR [ebx]
	test eax, -2147483648
	jne 2257f
2259:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2260:
	cmp edx, 32
	jae 2261f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2262f
2261:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2262:
	cmp edx, 0
	jne 2260b
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 4
	mov ecx, 0
2263:
	cmp edx, 32
	jae 2264f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2265f
2264:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2265:
	cmp edx, 0
	jne 2263b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+104]
	add eax, 1
	mov DWORD PTR [edi+104], eax
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 4
	mov eax, DWORD PTR [ebx]
	test eax, -2147483648
	je 2259b
	jmp 2258f
2257:
2258:
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 8
	mov eax, DWORD PTR [ebx+4]
	or eax, -2147483648
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+88], eax
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2266:
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
	jne 2266b
	mov edi, DWORD PTR [esp+44]
	mov DWORD PTR [edi+64], ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2267:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2267b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	add esi, ecx
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	sub ecx, 4
	sub esi, ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	je 2268f
2270:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2270b
	jmp 2269f
2268:
2269:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	add eax, 4
	shr eax, 2
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	sub eax, ecx
	add eax, 1
	mov DWORD PTR [edi+72], eax
2271:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+92], eax
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+80], eax
	mov ebp, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+84], eax
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [edi+92]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+24]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
2272:
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
	jne 2272b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [esp+24]
	add eax, 3
	shr eax, 2
	add eax, eax
	add eax, eax
	add ebp, eax
	mov eax, DWORD PTR [ebp]
	add eax, eax
	sbb eax, eax
	add eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+108], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
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
2273:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2273b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
2274:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2274b
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2271b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub esi, edx
	add esi, 8
2275:
	mov eax, 0
	mov DWORD PTR [esi], eax
	add esi, 4
	sub edx, 4
	jne 2275b
	mov eax, DWORD PTR [edi+104]
	test eax, eax
	je 2276f
2278:
	mov ebx, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
2279:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2279b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+104]
	sub eax, 1
	mov DWORD PTR [edi+104], eax
	jne 2278b
	jmp 2277f
2276:
2277:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2280:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2280b
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2281f
	jmp 2282f
2281:
2283:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2283b
2282:
	and edi, 15
	jne 2284f
	jmp 2285f
2284:
2286:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2286b
2285:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2287:
	cmp edx, 32
	jae 2288f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2289f
2288:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2289:
	cmp edx, 0
	jne 2287b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+16], ebx
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2290f
	jmp 2291f
2290:
2292:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2292b
2291:
	and edi, 15
	jne 2293f
	jmp 2294f
2293:
2295:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2295b
2294:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, 0
2296:
	cmp edx, 32
	jae 2297f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2298f
2297:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2298:
	cmp edx, 0
	jne 2296b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, 0
2299:
	cmp edx, 32
	jae 2300f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2301f
2300:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2301:
	cmp edx, 0
	jne 2299b
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2302:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2302b
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2303f
	jmp 2304f
2303:
2305:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2305b
2304:
	and edi, 15
	jne 2306f
	jmp 2307f
2306:
2308:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2308b
2307:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2309:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2309b
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2310f
	jmp 2311f
2310:
2312:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2312b
2311:
	and edi, 15
	jne 2313f
	jmp 2314f
2313:
2315:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2315b
2314:
	mov edi, DWORD PTR [esp+44]
	mov eax, 512
	mov DWORD PTR [edi+120], eax
2316:
	mov eax, DWORD PTR [esp+24]
	add eax, 3
	shr eax, 2
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [edi+120]
	cmp ecx, eax
	jb 2317f
	jmp 2318f
2317:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	add esi, edx
	mov edx, DWORD PTR [edi+120]
	sub esi, edx
	mov ecx, 0
2319:
	or ecx, DWORD PTR [esi]
	add esi, 4
	sub edx, 4
	jne 2319b
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2320:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2320b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [edi+120]
	add ebp, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov eax, DWORD PTR [edi+120]
	sub edx, eax
2321:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2321b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2322f
	jmp 2323f
2322:
2324:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2324b
2323:
	and edi, 15
	jne 2325f
	jmp 2326f
2325:
2327:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2327b
2326:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2328:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2328b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [edi+120]
	add ebp, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov eax, DWORD PTR [edi+120]
	sub edx, eax
2329:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2329b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2330f
	jmp 2331f
2330:
2332:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2332b
2331:
	and edi, 15
	jne 2333f
	jmp 2334f
2333:
2335:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2335b
2334:
	mov edi, DWORD PTR [esp+44]
2318:
	mov eax, DWORD PTR [edi+120]
	shr eax, 1
	mov DWORD PTR [edi+120], eax
	cmp eax, 4
	jae 2316b
	mov eax, 16
	mov DWORD PTR [edi+128], eax
2336:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	add esi, edx
	sub esi, 4
	mov eax, DWORD PTR [esi]
	mov ecx, eax
	mov edx, DWORD PTR [edi+128]
2337:
	add eax, eax
	sub edx, 1
	jne 2337b
	mov edx, DWORD PTR [edi+128]
2338:
	shr eax, 1
	sub edx, 1
	jne 2338b
	xor ecx, eax
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2339f
	jmp 2340f
2339:
2341:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2341b
2340:
	and edi, 15
	jne 2342f
	jmp 2343f
2342:
2344:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2344b
2343:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+100], eax
2345:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2346:
	cmp edx, 32
	jae 2347f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2348f
2347:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2348:
	cmp edx, 0
	jne 2346b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+100]
	sub eax, 1
	mov DWORD PTR [edi+100], eax
	jne 2345b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2349f
	jmp 2350f
2349:
2351:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2351b
2350:
	and edi, 15
	jne 2352f
	jmp 2353f
2352:
2354:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2354b
2353:
	mov edi, DWORD PTR [esp+44]
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2355f
	jmp 2356f
2355:
2357:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2357b
2356:
	and edi, 15
	jne 2358f
	jmp 2359f
2358:
2360:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2360b
2359:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+100], eax
2361:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2362:
	cmp edx, 32
	jae 2363f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2364f
2363:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2364:
	cmp edx, 0
	jne 2362b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+100]
	sub eax, 1
	mov DWORD PTR [edi+100], eax
	jne 2361b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2365f
	jmp 2366f
2365:
2367:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2367b
2366:
	and edi, 15
	jne 2368f
	jmp 2369f
2368:
2370:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2370b
2369:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	shr eax, 1
	mov DWORD PTR [edi+128], eax
	cmp eax, 1
	jae 2336b
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 8
	mov eax, DWORD PTR [ebx+4]
	or eax, -2147483648
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+88], eax
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2371:
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
	jne 2371b
	mov edi, DWORD PTR [esp+44]
	mov DWORD PTR [edi+64], ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2372:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2372b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add esi, ecx
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	sub ecx, 4
	sub esi, ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	je 2373f
2375:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2375b
	jmp 2374f
2373:
2374:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	shr eax, 2
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	sub eax, ecx
	add eax, 1
	mov DWORD PTR [edi+72], eax
2376:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+92], eax
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+80], eax
	mov ebp, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+84], eax
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [edi+92]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+24]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
2377:
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
	jne 2377b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [esp+24]
	add eax, 3
	shr eax, 2
	add eax, eax
	add eax, eax
	add ebp, eax
	mov eax, DWORD PTR [ebp]
	add eax, eax
	sbb eax, eax
	add eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+108], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
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
2378:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2378b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
2379:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2379b
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2376b
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2380f
	jmp 2381f
2380:
2382:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2382b
2381:
	and edi, 15
	jne 2383f
	jmp 2384f
2383:
2385:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2385b
2384:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, 0
2386:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 2386b
	mov eax, 0
	sub eax, ecx
	or eax, ecx
	shr eax, 31
	xor eax, 1
	mov DWORD PTR [edi+20], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, 0
2387:
	cmp edx, 32
	jae 2388f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2389f
2388:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2389:
	cmp edx, 0
	jne 2387b
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	add ecx, 4
	mov eax, 0
2390:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2390b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	add ecx, 4
	mov eax, 0
2391:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2391b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
2392:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+96]
	add eax, eax
	add eax, eax
	add ebx, eax
	mov ecx, DWORD PTR [ebx]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add ebp, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov ebx, 0
2393:
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2393b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	shr ecx, 2
	cmp eax, ecx
	jne 2392b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2394:
	cmp edx, 32
	jae 2395f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2396f
2395:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2396:
	cmp edx, 0
	jne 2394b
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2397:
	cmp edx, 32
	jae 2398f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2399f
2398:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2399:
	cmp edx, 0
	jne 2397b
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2400:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2400b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2401:
	cmp edx, 32
	jae 2402f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2403f
2402:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2403:
	cmp edx, 0
	jne 2401b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+24], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2404:
	cmp edx, 32
	jae 2405f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2406f
2405:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2406:
	cmp edx, 0
	jne 2404b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi+24]
	or eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+32]
	xor eax, 1
	mov DWORD PTR [edi+32], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
	sub esi, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov eax, DWORD PTR [esp+24]
	add eax, 3
	shr eax, 2
	add eax, eax
	add eax, eax
	sub edx, eax
	sub edx, eax
	je 2407f
2409:
	mov eax, 0
	mov DWORD PTR [esi], eax
	add esi, 4
	sub edx, 4
	jne 2409b
	jmp 2408f
2407:
2408:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2410:
	or ecx, DWORD PTR [esi]
	add esi, 4
	sub edx, 4
	jne 2410b
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+124], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	or eax, DWORD PTR [esi]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [edi+104], eax
	mov DWORD PTR [edi+108], eax
	mov eax, 1024
	mov DWORD PTR [edi+120], eax
2411:
	mov eax, DWORD PTR [esp+24]
	add eax, 3
	shr eax, 2
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [edi+120]
	cmp ecx, eax
	jb 2412f
	jmp 2413f
2412:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [edi+120]
	sub esi, edx
	mov ecx, 0
2414:
	or ecx, DWORD PTR [esi]
	add esi, 4
	sub edx, 4
	jne 2414b
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov edx, 0
	sub edx, DWORD PTR [edi+112]
	mov eax, DWORD PTR [edi+120]
	shr eax, 2
	and edx, eax
	add edx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2415:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2415b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [edi+120]
	add ebp, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov eax, DWORD PTR [edi+120]
	sub edx, eax
2416:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2416b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2417f
	jmp 2418f
2417:
2419:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2419b
2418:
	and edi, 15
	jne 2420f
	jmp 2421f
2420:
2422:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2422b
2421:
	mov edi, DWORD PTR [esp+44]
2413:
	mov eax, DWORD PTR [edi+120]
	shr eax, 1
	mov DWORD PTR [edi+120], eax
	cmp eax, 4
	jae 2411b
	mov eax, 16
	mov DWORD PTR [edi+128], eax
2423:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
	sub esi, 4
	mov eax, DWORD PTR [esi]
	mov ecx, eax
	mov edx, DWORD PTR [edi+128]
2424:
	add eax, eax
	sub edx, 1
	jne 2424b
	mov edx, DWORD PTR [edi+128]
2425:
	shr eax, 1
	sub edx, 1
	jne 2425b
	xor ecx, eax
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov edx, 0
	sub edx, DWORD PTR [edi+112]
	and edx, DWORD PTR [edi+128]
	add edx, DWORD PTR [edi+108]
	mov DWORD PTR [edi+108], edx
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2426f
	jmp 2427f
2426:
2428:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2428b
2427:
	and edi, 15
	jne 2429f
	jmp 2430f
2429:
2431:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2431b
2430:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+100], eax
2432:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2433:
	cmp edx, 32
	jae 2434f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2435f
2434:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2435:
	cmp edx, 0
	jne 2433b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+100]
	sub eax, 1
	mov DWORD PTR [edi+100], eax
	jne 2432b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2436f
	jmp 2437f
2436:
2438:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2438b
2437:
	and edi, 15
	jne 2439f
	jmp 2440f
2439:
2441:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2441b
2440:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	shr eax, 1
	mov DWORD PTR [edi+128], eax
	cmp eax, 2
	jae 2423b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2442:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2442b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	add eax, edx
	add eax, edx
	sub eax, 4
	mov ebp, DWORD PTR [eax]
	sub eax, 4
	mov edx, DWORD PTR [eax]
	mov DWORD PTR [edi+36], edx
	mov ebx, 0
	mov ecx, 0
	mov esi, 0
	mov eax, 32
	mov DWORD PTR [edi+48], eax
2443:
	mov eax, ecx
	shr eax, 30
	add esi, esi
	add esi, esi
	add esi, eax
	mov eax, ebp
	shr eax, 30
	add ecx, ecx
	add ecx, ecx
	add ecx, eax
	mov edx, DWORD PTR [edi+36]
	mov eax, edx
	shr eax, 30
	add ebp, ebp
	add ebp, ebp
	add ebp, eax
	add edx, edx
	add edx, edx
	mov DWORD PTR [edi+36], edx
	mov eax, ebx
	add eax, eax
	add eax, eax
	or eax, 1
	mov DWORD PTR [edi+40], eax
	mov edx, ebx
	shr edx, 30
	mov DWORD PTR [edi+44], edx
	cmp ecx, eax
	mov eax, esi
	sbb eax, edx
	sbb eax, eax
	xor eax, -1
	mov edx, DWORD PTR [edi+40]
	and edx, eax
	mov DWORD PTR [edi+40], edx
	mov edx, DWORD PTR [edi+44]
	and edx, eax
	and eax, 1
	add ebx, ebx
	add ebx, eax
	mov eax, DWORD PTR [edi+40]
	sub ecx, eax
	sbb esi, edx
	mov eax, DWORD PTR [edi+48]
	sub eax, 1
	mov DWORD PTR [edi+48], eax
	jne 2443b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	add eax, edx
	add eax, edx
	sub eax, 4
	mov DWORD PTR [eax], esi
	sub eax, 4
	mov DWORD PTR [eax], ecx
	mov DWORD PTR [edi+60], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov edx, ebx
	add edx, edx
	mov DWORD PTR [eax], edx
	mov edx, ebx
	shr edx, 31
	mov DWORD PTR [eax+4], edx
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2444:
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
	jne 2444b
	mov edi, DWORD PTR [esp+44]
	mov DWORD PTR [edi+64], ecx
	mov eax, DWORD PTR [esp+24]
	add eax, 3
	shr eax, 2
	add eax, eax
	add eax, eax
	shr eax, 2
	sub eax, 1
	mov DWORD PTR [edi+96], eax
	je 2445f
2447:
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	add esi, edx
	sub esi, 16
	add ebx, edx
	sub ebx, 16
	mov ecx, DWORD PTR [esi+4]
	and ecx, 1
	ror ecx, 1
	mov eax, DWORD PTR [esi]
	shr eax, 1
	or eax, ecx
	mov DWORD PTR [edi+80], eax
	mov ecx, DWORD PTR [ebx+4]
	and ecx, 1
	ror ecx, 1
	mov eax, DWORD PTR [ebx]
	shr eax, 1
	or eax, ecx
	mov DWORD PTR [edi+88], eax
	mov ecx, DWORD PTR [esi+12]
	and ecx, 1
	ror ecx, 1
	mov eax, DWORD PTR [esi+8]
	shr eax, 1
	or eax, ecx
	mov DWORD PTR [edi+84], eax
	mov edx, eax
	mov ecx, DWORD PTR [esi+8]
	and ecx, 1
	ror ecx, 1
	mov eax, DWORD PTR [esi+4]
	shr eax, 1
	or eax, ecx
	mov ebp, eax
	mov eax, edx
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov ecx, DWORD PTR [edi+76]
	mov DWORD PTR [ebx], ecx
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	add eax, 8
	mov ebp, edi
	add ebp, 160
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	shr eax, 1
	shr eax, 1
	shr eax, 1
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov edi, edx
2448:
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
	jne 2448b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov eax, DWORD PTR [ebx]
	add eax, eax
	mov edx, DWORD PTR [ebx+4]
	adc edx, 0
	sub eax, 1
	sbb edx, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], edx
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	add eax, 8
	mov ebp, edi
	add ebp, 160
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	shr eax, 1
	shr eax, 1
	shr eax, 1
	mov eax, ebp
	add eax, edx
	mov eax, DWORD PTR [eax]
	add eax, eax
	sbb ecx, ecx
	mov DWORD PTR [edi+48], ecx
	mov esi, 0
	mov edi, edx
	add edi, 4
2449:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2449b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov ecx, DWORD PTR [edi+48]
	and ecx, 2
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebx+4]
	sub eax, ecx
	sbb edx, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], edx
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	add eax, 8
	mov ebp, edi
	add ebp, 160
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	shr eax, 1
	shr eax, 1
	shr eax, 1
	mov eax, ebp
	add eax, edx
	mov eax, DWORD PTR [eax]
	add eax, eax
	sbb ecx, ecx
	mov DWORD PTR [edi+48], ecx
	mov esi, 0
	mov edi, edx
	add edi, 4
2450:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2450b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov ecx, DWORD PTR [edi+48]
	and ecx, 2
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebx+4]
	sub eax, ecx
	sbb edx, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], edx
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	add eax, 8
	mov ebp, edi
	add ebp, 160
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	shr eax, 1
	shr eax, 1
	shr eax, 1
	mov eax, ebp
	add eax, edx
	mov eax, DWORD PTR [eax]
	add eax, eax
	sbb ecx, ecx
	mov DWORD PTR [edi+48], ecx
	mov esi, 0
	mov edi, edx
	add edi, 4
2451:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2451b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov ecx, DWORD PTR [edi+48]
	and ecx, 2
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebx+4]
	sub eax, ecx
	sbb edx, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], edx
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebx+4]
	add eax, 1
	adc edx, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], edx
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, eax
	add esi, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add ebx, eax
	mov edx, DWORD PTR [esp+24]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	sub edx, eax
	add edx, 8
	mov eax, DWORD PTR [esp+24]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 24
	add eax, 8
	mov ebp, edi
	add ebp, 160
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	add eax, eax
	add ebp, eax
	shr eax, 1
	shr eax, 1
	shr eax, 1
	add edx, 4
2452:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi], eax
	add ebp, 4
	add esi, 4
	sub edx, 4
	jne 2452b
	mov eax, DWORD PTR [edi+96]
	sub eax, 1
	mov DWORD PTR [edi+96], eax
	jne 2447b
	jmp 2446f
2445:
2446:
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov ecx, 0
2453:
	or ecx, DWORD PTR [esi]
	add esi, 4
	sub edx, 4
	jne 2453b
	mov eax, 0
	sub eax, ecx
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+52], eax
	mov ebx, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
2454:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2454b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, 512
	mov DWORD PTR [edi+120], eax
2455:
	mov eax, DWORD PTR [esp+24]
	add eax, 3
	shr eax, 2
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [edi+120]
	cmp ecx, eax
	jb 2456f
	jmp 2457f
2456:
	mov eax, DWORD PTR [edi+104]
	shr eax, 1
	mov edx, DWORD PTR [edi+120]
	shr edx, 2
	and eax, edx
	cmp eax, 1
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+24]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 24
	add ecx, 4
	mov eax, 0
2458:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2458b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [edi+120]
	add esi, edx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	mov eax, DWORD PTR [edi+120]
	sub edx, eax
2459:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2459b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2460f
	jmp 2461f
2460:
2462:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2462b
2461:
	and edi, 15
	jne 2463f
	jmp 2464f
2463:
2465:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2465b
2464:
	mov edi, DWORD PTR [esp+44]
2457:
	mov eax, DWORD PTR [edi+120]
	shr eax, 1
	mov DWORD PTR [edi+120], eax
	cmp eax, 4
	jae 2455b
	mov eax, DWORD PTR [edi+104]
	and eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [edi+108]
	shr edx, 1
	add eax, edx
	mov DWORD PTR [edi+108], eax
	mov eax, 16
	mov DWORD PTR [edi+128], eax
2466:
	mov eax, DWORD PTR [edi+108]
	and eax, DWORD PTR [edi+128]
	cmp eax, 1
	sbb eax, eax
	add eax, 1
	mov DWORD PTR [edi+112], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2467f
	jmp 2468f
2467:
2469:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2469b
2468:
	and edi, 15
	jne 2470f
	jmp 2471f
2470:
2472:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2472b
2471:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+100], eax
2473:
	mov ebx, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
2474:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2474b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+100]
	sub eax, 1
	mov DWORD PTR [edi+100], eax
	jne 2473b
	mov ecx, 0
	sub ecx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 24
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2475f
	jmp 2476f
2475:
2477:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2477b
2476:
	and edi, 15
	jne 2478f
	jmp 2479f
2478:
2480:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2480b
2479:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+128]
	shr eax, 1
	mov DWORD PTR [edi+128], eax
	cmp eax, 1
	jae 2466b
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 24
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [esi]
	sub eax, DWORD PTR [edi+124]
	mov DWORD PTR [esi], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2481f
	jmp 2482f
2481:
2483:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2483b
2482:
	and edi, 15
	jne 2484f
	jmp 2485f
2484:
2486:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2486b
2485:
	mov edi, DWORD PTR [esp+44]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, 0
2487:
	cmp edx, 32
	jae 2488f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2489f
2488:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2489:
	cmp edx, 0
	jne 2487b
	mov edi, DWORD PTR [esp+44]
	mov ebx, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
2490:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2490b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, 0
2491:
	cmp edx, 32
	jae 2492f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2493f
2492:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2493:
	cmp edx, 0
	jne 2491b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov ebx, 0
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
2494:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2494b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+144]
	and eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+132]
	and eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+132]
	and eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+132]
	and eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+132], eax
	mov ecx, DWORD PTR [edi+132]
	sub ecx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2495f
	jmp 2496f
2495:
2497:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2497b
2496:
	and edi, 15
	jne 2498f
	jmp 2499f
2498:
2500:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2500b
2499:
	mov edi, DWORD PTR [esp+44]
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
2501:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2501b
	mov ecx, DWORD PTR [edi+132]
	sub ecx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2502f
	jmp 2503f
2502:
2504:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2504b
2503:
	and edi, 15
	jne 2505f
	jmp 2506f
2505:
2507:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2507b
2506:
	mov edi, DWORD PTR [esp+44]
	mov ebx, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
2508:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2508b
	mov eax, DWORD PTR [edi+132]
21:
	mov ebx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi+4]
	mov esi, DWORD PTR [edi+8]
	mov edi, DWORD PTR [edi+12]
	ret
	.p2align 6

vg_rsa_check_key:
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], ebp
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov edi, eax
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
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
	mov eax, 0
	jmp 21f
20:
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov ebx, 0
	mov edx, 0
22:
	movzx eax, BYTE PTR [esi]
	mov ebp, ebx
	shr ebp, 24
	ror edx, 24
	and edx, -256
	add edx, ebp
	ror ebx, 24
	and ebx, -256
	add ebx, eax
	mov ebp, edx
	shr ebp, 1
	cmp ebp, 0
	je 23f
	mov edx, 2
	jmp 24f
23:
24:
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 22b
	mov ebp, edx
	shr ebp, 1
	mov eax, ebx
	and eax, 1
	xor eax, 1
	or ebp, eax
	cmp ebp, 0
	je 25f
	mov eax, 0
	jmp 26f
25:
	mov ebp, ebx
	xor ebp, 1
	or ebp, edx
	cmp ebp, 0
	je 27f
	mov eax, 1
	jmp 28f
27:
	mov eax, 0
28:
26:
	cmp eax, 0
	je 29f
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov ecx, 0
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov eax, 0
211:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 211b
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	add esi, ecx
	sub esi, 1
212:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 212b
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	add esi, ecx
	sub esi, 1
213:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 213b
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
214:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 214b
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
215:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 215b
	mov esi, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
216:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 216b
	mov esi, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [esp+48]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 217b
	mov esi, DWORD PTR [esp+52]
	mov ecx, DWORD PTR [esp+56]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
218:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 218b
	mov esi, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [esp+64]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
219:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 219b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, eax
	and ecx, 7
	mov edx, DWORD PTR [esp+32]
	add edx, edx
	sub edx, eax
	or ecx, edx
	mov edx, DWORD PTR [esp+40]
	add edx, edx
	sub edx, eax
	or ecx, edx
	cmp eax, 128
	sbb edx, edx
	or ecx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add ebx, eax
	sub ebx, 4
	mov eax, DWORD PTR [ebx]
	xor eax, -1
	shr eax, 31
	or ecx, eax
	mov DWORD PTR [edi+144], ecx
	mov eax, DWORD PTR [edi+144]
	cmp eax, 0
	je 220f
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
222:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 222b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
223:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 223b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
224:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+96]
	add eax, eax
	add eax, eax
	add ebx, eax
	mov ecx, DWORD PTR [ebx]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add ebp, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ebx, 0
225:
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 225b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	cmp eax, ecx
	jne 224b
	jmp 221f
220:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
226:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 226b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
227:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 227b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add eax, ecx
	mov ecx, 0
	mov DWORD PTR [eax+4], ecx
	mov eax, 0
	mov DWORD PTR [edi+96], eax
228:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+96]
	add eax, eax
	add eax, eax
	add ebx, eax
	mov ecx, DWORD PTR [ebx]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add ebp, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 1
	mov ebx, 0
229:
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 229b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	shr ecx, 1
	cmp eax, ecx
	jne 228b
221:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
230:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 230b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
231:
	or ecx, DWORD PTR [ebp]
	add ebp, 4
	sub edx, 4
	jne 231b
	mov eax, 0
	sub eax, ecx
	or eax, ecx
	shr eax, 31
	xor eax, 1
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 232f
	jmp 233f
232:
234:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 234b
233:
	and edi, 15
	jne 235f
	jmp 236f
235:
237:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 237b
236:
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	or ecx, 1
	xor ecx, 1
	mov DWORD PTR [eax], ecx
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 238f
	jmp 239f
238:
240:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 240b
239:
	and edi, 15
	jne 241f
	jmp 242f
241:
243:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 243b
242:
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	or ecx, 1
	xor ecx, 1
	mov DWORD PTR [eax], ecx
	mov eax, DWORD PTR [esp+8]
	mov ecx, eax
	and ecx, 7
	mov edx, DWORD PTR [esp+32]
	add edx, edx
	sub edx, eax
	or ecx, edx
	mov edx, DWORD PTR [esp+40]
	add edx, edx
	sub edx, eax
	or ecx, edx
	cmp eax, 128
	sbb edx, edx
	or ecx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add ebx, eax
	sub ebx, 4
	mov eax, DWORD PTR [ebx]
	xor eax, -1
	shr eax, 31
	or ecx, eax
	mov DWORD PTR [edi+144], ecx
	mov eax, DWORD PTR [edi+144]
	cmp eax, 0
	je 244f
	mov esi, 3
246:
	cmp esi, 3
	je 247f
	cmp esi, 2
	je 249f
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 251f
	jmp 252f
251:
253:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 253b
252:
	and edi, 15
	jne 254f
	jmp 255f
254:
256:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 256b
255:
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 257f
	jmp 258f
257:
259:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 259b
258:
	and edi, 15
	jne 260f
	jmp 261f
260:
262:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 262b
261:
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 263f
	jmp 264f
263:
265:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 265b
264:
	and edi, 15
	jne 266f
	jmp 267f
266:
268:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 268b
267:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+40]
	ror eax, 13
	add esi, eax
	jmp 250f
249:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 269f
	jmp 270f
269:
271:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 271b
270:
	and edi, 15
	jne 272f
	jmp 273f
272:
274:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 274b
273:
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 275f
	jmp 276f
275:
277:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 277b
276:
	and edi, 15
	jne 278f
	jmp 279f
278:
280:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 280b
279:
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 281f
	jmp 282f
281:
283:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 283b
282:
	and edi, 15
	jne 284f
	jmp 285f
284:
286:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 286b
285:
	mov edi, DWORD PTR [esp+68]
	add esi, 2162688
250:
	jmp 248f
247:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 287f
	jmp 288f
287:
289:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 289b
288:
	and edi, 15
	jne 290f
	jmp 291f
290:
292:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 292b
291:
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 293f
	jmp 294f
293:
295:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 295b
294:
	and edi, 15
	jne 296f
	jmp 297f
296:
298:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 298b
297:
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 299f
	jmp 2100f
299:
2101:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2101b
2100:
	and edi, 15
	jne 2102f
	jmp 2103f
2102:
2104:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2104b
2103:
	mov edi, DWORD PTR [esp+68]
	add esi, 2162688
248:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2105:
	cmp edx, 32
	jae 2106f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2107f
2106:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2107:
	cmp edx, 0
	jne 2105b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2108f
	jmp 2109f
2108:
2110:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2110b
2109:
	and edi, 15
	jne 2111f
	jmp 2112f
2111:
2113:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2113b
2112:
	mov edi, DWORD PTR [esp+68]
2114:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+104], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2115f
	jmp 2116f
2115:
2117:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 2117b
2116:
	and edx, 15
	jne 2118f
	jmp 2119f
2118:
2120:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2120b
2119:
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2121:
	cmp edx, 32
	jae 2122f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2123f
2122:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2123:
	cmp edx, 0
	jne 2121b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2124:
	cmp edx, 32
	jae 2125f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2126f
2125:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2126:
	cmp edx, 0
	jne 2124b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2127:
	cmp edx, 32
	jae 2128f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2129f
2128:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2129:
	cmp edx, 0
	jne 2127b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+108], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2130f
	jmp 2131f
2130:
2132:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 2132b
2131:
	and edx, 15
	jne 2133f
	jmp 2134f
2133:
2135:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2135b
2134:
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2136:
	cmp edx, 32
	jae 2137f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2138f
2137:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2138:
	cmp edx, 0
	jne 2136b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2139:
	cmp edx, 32
	jae 2140f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2141f
2140:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2141:
	cmp edx, 0
	jne 2139b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2142:
	cmp edx, 32
	jae 2143f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2144f
2143:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2144:
	cmp edx, 0
	jne 2142b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+108], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2145f
	jmp 2146f
2145:
2147:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	add ebp, 16
	add ebx, 16
	add edi, 16
	sub eax, 1
	jne 2147b
2146:
	and edx, 15
	jne 2148f
	jmp 2149f
2148:
2150:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2150b
2149:
	mov edi, DWORD PTR [esp+68]
	mov ebx, 0
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
2151:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2151b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	sub esi, 65536
	cmp esi, 65536
	jae 2114b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2152:
	cmp edx, 32
	jae 2153f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2154f
2153:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2154:
	cmp edx, 0
	jne 2152b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2155:
	cmp edx, 32
	jae 2156f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2157f
2156:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2157:
	cmp edx, 0
	jne 2155b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	sub esi, 1
	cmp esi, 0
	jne 246b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2158:
	cmp edx, 32
	jae 2159f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2160f
2159:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2160:
	cmp edx, 0
	jne 2158b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2161f
	jmp 2162f
2161:
2163:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2163b
2162:
	and edi, 15
	jne 2164f
	jmp 2165f
2164:
2166:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2166b
2165:
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2167f
	jmp 2168f
2167:
2169:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2169b
2168:
	and edi, 15
	jne 2170f
	jmp 2171f
2170:
2172:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2172b
2171:
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2173:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2173b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2174:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2175:
	cmp edx, 32
	jae 2176f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2177f
2176:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2177:
	cmp edx, 0
	jne 2175b
	mov edi, DWORD PTR [esp+68]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2178:
	cmp edx, 32
	jae 2179f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2180f
2179:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2180:
	cmp edx, 0
	jne 2178b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2181:
	cmp edx, 32
	jae 2182f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2183f
2182:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2183:
	cmp edx, 0
	jne 2181b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2184f
	jmp 2185f
2184:
2186:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2186b
2185:
	and edi, 15
	jne 2187f
	jmp 2188f
2187:
2189:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2189b
2188:
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
	jne 2174b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2190:
	cmp edx, 32
	jae 2191f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2192f
2191:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2192:
	cmp edx, 0
	jne 2190b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2193:
	cmp edx, 32
	jae 2194f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2195f
2194:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2195:
	cmp edx, 0
	jne 2193b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2196f
	jmp 2197f
2196:
2198:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2198b
2197:
	and edi, 15
	jne 2199f
	jmp 2200f
2199:
2201:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2201b
2200:
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2202f
	jmp 2203f
2202:
2204:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2204b
2203:
	and edi, 15
	jne 2205f
	jmp 2206f
2205:
2207:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2207b
2206:
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2208:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2208b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2209:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2210:
	cmp edx, 32
	jae 2211f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2212f
2211:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2212:
	cmp edx, 0
	jne 2210b
	mov edi, DWORD PTR [esp+68]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2213:
	cmp edx, 32
	jae 2214f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2215f
2214:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2215:
	cmp edx, 0
	jne 2213b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2216:
	cmp edx, 32
	jae 2217f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2218f
2217:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2218:
	cmp edx, 0
	jne 2216b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2219f
	jmp 2220f
2219:
2221:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2221b
2220:
	and edi, 15
	jne 2222f
	jmp 2223f
2222:
2224:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2224b
2223:
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
	jne 2209b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2225:
	cmp edx, 32
	jae 2226f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2227f
2226:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2227:
	cmp edx, 0
	jne 2225b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2228:
	cmp edx, 32
	jae 2229f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2230f
2229:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2230:
	cmp edx, 0
	jne 2228b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	jmp 245f
244:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2231:
	cmp edx, 32
	jae 2232f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2233f
2232:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2233:
	cmp edx, 0
	jne 2231b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2234:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2234b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2235:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2235b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
2236:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov eax, DWORD PTR [edi+96]
	add eax, eax
	add eax, eax
	add ebx, eax
	mov ecx, DWORD PTR [ebx]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add ebp, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ebx, 0
2237:
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2237b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	cmp eax, 2
	jne 2236b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 8
	mov eax, DWORD PTR [ebx+4]
	or eax, -2147483648
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+88], eax
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2238:
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
	jne 2238b
	mov edi, DWORD PTR [esp+68]
	mov DWORD PTR [edi+64], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2239:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2239b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	add esi, ecx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	sub ecx, 4
	sub esi, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	je 2240f
2242:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2242b
	jmp 2241f
2240:
2241:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+32]
	add eax, 3
	shr eax, 2
	add eax, eax
	add eax, eax
	add eax, 8
	shr eax, 2
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	sub eax, ecx
	add eax, 1
	mov DWORD PTR [edi+72], eax
2243:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+92], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+80], eax
	mov ebp, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+84], eax
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [edi+92]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
2244:
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
	jne 2244b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
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
2245:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2245b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
2246:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2246b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2243b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2247:
	cmp edx, 32
	jae 2248f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2249f
2248:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2249:
	cmp edx, 0
	jne 2247b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2250:
	cmp edx, 32
	jae 2251f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2252f
2251:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2252:
	cmp edx, 0
	jne 2250b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2253:
	cmp edx, 32
	jae 2254f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2255f
2254:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2255:
	cmp edx, 0
	jne 2253b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2256:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2256b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2257:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2257b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
2258:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov eax, DWORD PTR [edi+96]
	add eax, eax
	add eax, eax
	add ebx, eax
	mov ecx, DWORD PTR [ebx]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add ebp, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ebx, 0
2259:
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2259b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	cmp eax, 2
	jne 2258b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 8
	mov eax, DWORD PTR [ebx+4]
	or eax, -2147483648
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+88], eax
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2260:
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
	jne 2260b
	mov edi, DWORD PTR [esp+68]
	mov DWORD PTR [edi+64], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2261:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2261b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	add esi, ecx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	sub ecx, 4
	sub esi, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	je 2262f
2264:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2264b
	jmp 2263f
2262:
2263:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+32]
	add eax, 3
	shr eax, 2
	add eax, eax
	add eax, eax
	add eax, 8
	shr eax, 2
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	sub eax, ecx
	add eax, 1
	mov DWORD PTR [edi+72], eax
2265:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+92], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+80], eax
	mov ebp, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+84], eax
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [edi+92]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
2266:
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
	jne 2266b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
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
2267:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2267b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
2268:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2268b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2265b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2269:
	cmp edx, 32
	jae 2270f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2271f
2270:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2271:
	cmp edx, 0
	jne 2269b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2272:
	cmp edx, 32
	jae 2273f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2274f
2273:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2274:
	cmp edx, 0
	jne 2272b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2275:
	cmp edx, 32
	jae 2276f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2277f
2276:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2277:
	cmp edx, 0
	jne 2275b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2278:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2278b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2279:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2279b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add eax, ecx
	mov ecx, 0
	mov DWORD PTR [eax+4], ecx
	mov eax, 0
	mov DWORD PTR [edi+96], eax
2280:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+96]
	add eax, eax
	add eax, eax
	add ebx, eax
	mov ecx, DWORD PTR [ebx]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add ebp, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 1
	mov ebx, 0
2281:
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2281b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	shr ecx, 1
	cmp eax, ecx
	jne 2280b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 8
	mov eax, DWORD PTR [ebx+4]
	or eax, -2147483648
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+88], eax
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2282:
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
	jne 2282b
	mov edi, DWORD PTR [esp+68]
	mov DWORD PTR [edi+64], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2283:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2283b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add esi, ecx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	sub ecx, 4
	sub esi, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	je 2284f
2286:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2286b
	jmp 2285f
2284:
2285:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 2
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	sub eax, ecx
	add eax, 1
	mov DWORD PTR [edi+72], eax
2287:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+92], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+80], eax
	mov ebp, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+84], eax
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [edi+92]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
2288:
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
	jne 2288b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
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
2289:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2289b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
2290:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2290b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2287b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2291:
	cmp edx, 32
	jae 2292f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2293f
2292:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2293:
	cmp edx, 0
	jne 2291b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2294:
	cmp edx, 32
	jae 2295f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2296f
2295:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2296:
	cmp edx, 0
	jne 2294b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2297:
	cmp edx, 32
	jae 2298f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2299f
2298:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2299:
	cmp edx, 0
	jne 2297b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 8
	mov eax, DWORD PTR [ebx+4]
	or eax, -2147483648
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+88], eax
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2300:
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
	jne 2300b
	mov edi, DWORD PTR [esp+68]
	mov DWORD PTR [edi+64], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2301:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2301b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add esi, ecx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	sub ecx, 4
	sub esi, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	je 2302f
2304:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2304b
	jmp 2303f
2302:
2303:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 2
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	sub eax, ecx
	add eax, 1
	mov DWORD PTR [edi+72], eax
2305:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+92], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+80], eax
	mov ebp, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+84], eax
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [edi+92]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
2306:
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
	jne 2306b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
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
2307:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2307b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
2308:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2308b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2305b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2309:
	cmp edx, 32
	jae 2310f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2311f
2310:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2311:
	cmp edx, 0
	jne 2309b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2312:
	cmp edx, 32
	jae 2313f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2314f
2313:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2314:
	cmp edx, 0
	jne 2312b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 8
	mov eax, DWORD PTR [ebx+4]
	or eax, -2147483648
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+88], eax
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2315:
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
	jne 2315b
	mov edi, DWORD PTR [esp+68]
	mov DWORD PTR [edi+64], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2316:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2316b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add esi, ecx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	sub ecx, 4
	sub esi, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	je 2317f
2319:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2319b
	jmp 2318f
2317:
2318:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 2
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	sub eax, ecx
	add eax, 1
	mov DWORD PTR [edi+72], eax
2320:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+92], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+80], eax
	mov ebp, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+84], eax
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [edi+92]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
2321:
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
	jne 2321b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
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
2322:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2322b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
2323:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2323b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2320b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2324:
	cmp edx, 32
	jae 2325f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2326f
2325:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2326:
	cmp edx, 0
	jne 2324b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2327:
	cmp edx, 32
	jae 2328f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2329f
2328:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2329:
	cmp edx, 0
	jne 2327b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
245:
	mov eax, DWORD PTR [edi+120]
	jmp 210f
29:
	mov eax, 0
210:
21:
	mov ebx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi+4]
	mov esi, DWORD PTR [edi+8]
	mov edi, DWORD PTR [edi+12]
	ret
	.p2align 6

vg_rsa_crt_values:
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], ebp
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov edi, eax
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
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
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov eax, 0
23:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 23b
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov eax, 0
24:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 24b
	jmp 21f
20:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov ecx, 0
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	add ecx, edx
	mov eax, 0
25:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 25b
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
26:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 26b
	mov esi, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	mov esi, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [esp+48]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
28:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 28b
	mov esi, DWORD PTR [esp+52]
	mov ecx, DWORD PTR [esp+56]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
29:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 29b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [esp+32]
	mov ecx, eax
	and ecx, 7
	mov edx, DWORD PTR [esp+40]
	add edx, edx
	sub edx, eax
	or ecx, edx
	mov edx, DWORD PTR [esp+48]
	add edx, edx
	sub edx, eax
	or ecx, edx
	cmp eax, 128
	sbb edx, edx
	or ecx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [esp+32]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add ebx, eax
	sub ebx, 4
	mov eax, DWORD PTR [ebx]
	xor eax, -1
	shr eax, 31
	or ecx, eax
	mov DWORD PTR [edi+144], ecx
	mov eax, DWORD PTR [edi+144]
	cmp eax, 0
	je 210f
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
212:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 212b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
213:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 213b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
214:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+96]
	add eax, eax
	add eax, eax
	add ebx, eax
	mov ecx, DWORD PTR [ebx]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add ebp, eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov ebx, 0
215:
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 215b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	cmp eax, ecx
	jne 214b
	jmp 211f
210:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
216:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 216b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
217:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 217b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add eax, ecx
	mov ecx, 0
	mov DWORD PTR [eax+4], ecx
	mov eax, 0
	mov DWORD PTR [edi+96], eax
218:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+96]
	add eax, eax
	add eax, eax
	add ebx, eax
	mov ecx, DWORD PTR [ebx]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add ebp, eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	shr edi, 1
	mov ebx, 0
219:
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 219b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	shr ecx, 1
	cmp eax, ecx
	jne 218b
211:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
220:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 220b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
221:
	or ecx, DWORD PTR [ebp]
	add ebp, 4
	sub edx, 4
	jne 221b
	mov eax, 0
	sub eax, ecx
	or eax, ecx
	shr eax, 31
	xor eax, 1
	mov DWORD PTR [edi+120], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 222f
	jmp 223f
222:
224:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 224b
223:
	and edi, 15
	jne 225f
	jmp 226f
225:
227:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 227b
226:
	mov edi, DWORD PTR [esp+60]
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 228f
	jmp 229f
228:
230:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 230b
229:
	and edi, 15
	jne 231f
	jmp 232f
231:
233:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 233b
232:
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	or ecx, 1
	mov DWORD PTR [eax], ecx
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 234f
	jmp 235f
234:
236:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 236b
235:
	and edi, 15
	jne 237f
	jmp 238f
237:
239:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 239b
238:
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	shr edx, 1
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
240:
	cmp edx, 32
	jae 241f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 242f
241:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
242:
	cmp edx, 0
	jne 240b
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [esp+32]
	and eax, 15
	je 243f
	cmp eax, eax
	jmp 244f
243:
	mov eax, DWORD PTR [esp+32]
	cmp eax, 128
	jae 245f
	cmp eax, eax
	jmp 246f
245:
	mov eax, DWORD PTR [esp+32]
	shr eax, 1
	add eax, 1
	mov ecx, DWORD PTR [esp+40]
	cmp ecx, eax
	jb 247f
	cmp eax, eax
	jmp 248f
247:
	mov ecx, DWORD PTR [esp+48]
	cmp ecx, eax
248:
246:
244:
	jb 249f
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
251:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 251b
	mov eax, 0
	sub eax, ecx
	or eax, ecx
	shr eax, 31
	xor eax, 1
	mov DWORD PTR [edi+16], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+16]
	add ecx, DWORD PTR [edi+16]
	mov DWORD PTR [eax], ecx
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 252f
	jmp 253f
252:
254:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 254b
253:
	and edi, 15
	jne 255f
	jmp 256f
255:
257:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 257b
256:
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
258:
	cmp edx, 32
	jae 259f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 260f
259:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
260:
	cmp edx, 0
	jne 258b
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [esp+32]
	mov ecx, eax
	add ecx, 7
	shr ecx, 3
	mov edx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	sub ecx, edx
	add ecx, 35
	push eax
	push ecx
	push edi
	call {vg_rsa_keygen_inverse}
	pop eax
	pop eax
	pop eax
	jmp 250f
249:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	mov DWORD PTR [edi+52], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	mov DWORD PTR [edi+56], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	shr edx, 1
	mov DWORD PTR [edi+60], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+64], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+68], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+72], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+76], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+80], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+84], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+88], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [esp+32]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 1
	mov DWORD PTR [edi+96], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ebx, DWORD PTR [edi+60]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 261f
	jmp 262f
261:
263:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 263b
262:
	and edi, 15
	jne 264f
	jmp 265f
264:
266:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 266b
265:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+60]
	mov eax, DWORD PTR [ebp]
	xor eax, 1
	mov ebx, ebp
	add ebx, 4
	mov esi, DWORD PTR [edi+96]
	sub esi, 4
267:
	or eax, DWORD PTR [ebx]
	add ebx, 4
	sub esi, 4
	jne 267b
	sub eax, 1
	sbb eax, eax
	and eax, 2
	mov ecx, DWORD PTR [ebp]
	or ecx, eax
	mov DWORD PTR [ebp], ecx
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov ecx, -1
	mov ebp, DWORD PTR [edi+52]
	mov ebx, DWORD PTR [edi+76]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 268f
	jmp 269f
268:
270:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 270b
269:
	and edi, 15
	jne 271f
	jmp 272f
271:
273:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 273b
272:
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov ebp, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
274:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 274b
	mov ecx, DWORD PTR [edi+160]
	and ecx, 1
	sub ecx, 1
	mov ebp, DWORD PTR [edi+60]
	mov ebx, DWORD PTR [edi+84]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 275f
	jmp 276f
275:
277:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 277b
276:
	and edi, 15
	jne 278f
	jmp 279f
278:
280:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 280b
279:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+76]
	mov ebx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+76]
	mov ecx, 0
281:
	cmp edx, 32
	jae 282f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 283f
282:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
283:
	cmp edx, 0
	jne 281b
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov ebp, DWORD PTR [edi+60]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
284:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi], eax
	add ebp, 4
	add esi, 16
	sub ecx, 1
	jne 284b
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov ebp, DWORD PTR [edi+76]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
285:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi+4], eax
	add ebp, 4
	add esi, 16
	sub ecx, 1
	jne 285b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
286:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 286b
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
287:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi], eax
	add ebp, 4
	add esi, 20
	sub ecx, 1
	jne 287b
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
288:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi+4], eax
	add ebp, 4
	add esi, 20
	sub ecx, 1
	jne 288b
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov ebp, DWORD PTR [edi+60]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
289:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi+16], eax
	add ebp, 4
	add esi, 20
	sub ecx, 1
	jne 289b
	mov eax, DWORD PTR [edi+80]
	add eax, 20
	mov ecx, 1
	mov DWORD PTR [eax+4], ecx
	mov eax, 1
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+60]
	mov ebx, DWORD PTR [eax]
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
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+96]
	add eax, 0
	shr eax, 2
	mov ecx, eax
	add eax, ecx
	add eax, ecx
	add eax, 2
	shr eax, 1
	mov DWORD PTR [edi+100], eax
290:
	mov ebx, DWORD PTR [edi+64]
	add ebx, 16
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+24], eax
	mov eax, 1
	mov DWORD PTR [edi+28], eax
	mov eax, 0
	mov DWORD PTR [edi+32], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov eax, 1
	mov DWORD PTR [edi+40], eax
	mov esi, 30
291:
	sub esi, 1
	mov eax, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+16]
	mov ebx, edx
	and eax, 1
	mov ecx, 0
	sub ecx, eax
	shr edx, 31
	sub edx, 1
	and edx, ecx
	mov eax, ebx
	xor eax, edx
	sub eax, edx
	add eax, 2
	mov DWORD PTR [edi+16], eax
	mov ebx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [edi+24]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	shr eax, 1
	mov DWORD PTR [edi+20], ebx
	mov DWORD PTR [edi+24], eax
	mov ebx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+36]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+28], ebx
	mov DWORD PTR [edi+36], eax
	mov ebx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [edi+40]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+32], ebx
	mov DWORD PTR [edi+40], eax
	test esi, esi
	jne 291b
	mov eax, DWORD PTR [edi+28]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+32]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+36]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+40]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+172], eax
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
292:
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+8], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 292b
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+28]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+32]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967288], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
293:
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967292], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+12], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 293b
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967292], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+36]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+40]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967292], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov ebx, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+4]
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add esi, eax
	mov eax, DWORD PTR [esi]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [esi+4]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+188], eax
	mov esi, DWORD PTR [edi+28]
	and esi, DWORD PTR [edi+184]
	mov eax, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+188]
	add esi, eax
	mov eax, DWORD PTR [edi+28]
	mul ebx
	mov ebp, eax
	mov eax, DWORD PTR [edi+32]
	mul ecx
	add ebp, eax
	mov eax, DWORD PTR [edi+44]
	mul ebp
	mov edx, esi
	sub edx, eax
	and edx, 1073741823
	sub esi, edx
	mov DWORD PTR [edi+192], esi
	mov esi, DWORD PTR [edi+36]
	and esi, DWORD PTR [edi+184]
	mov eax, DWORD PTR [edi+40]
	and eax, DWORD PTR [edi+188]
	add esi, eax
	mov eax, DWORD PTR [edi+36]
	mul ebx
	mov ebp, eax
	mov eax, DWORD PTR [edi+40]
	mul ecx
	add ebp, eax
	mov eax, DWORD PTR [edi+44]
	mul ebp
	mov edx, esi
	sub edx, eax
	and edx, 1073741823
	sub esi, edx
	mov DWORD PTR [edi+196], esi
	mov eax, DWORD PTR [edi+192]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+196]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+204], eax
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov DWORD PTR [edi+176], ebx
294:
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+200]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967284], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+24]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [esi+36]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+36]
	and eax, DWORD PTR [edi+200]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+8], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 40
	cmp esi, DWORD PTR [edi+180]
	jne 294b
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+200]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967284], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 20
	mov eax, DWORD PTR [esi+4294967276]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+28]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+32]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967284], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov DWORD PTR [edi+176], ebx
295:
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+204]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+24]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [esi+36]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+36]
	and eax, DWORD PTR [edi+204]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+12], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 40
	cmp esi, DWORD PTR [edi+180]
	jne 295b
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+204]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 20
	mov eax, DWORD PTR [esi+4294967276]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+36]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+40]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967288], ebx
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+64]
	add ebx, 16
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+24], eax
	mov eax, 1
	mov DWORD PTR [edi+28], eax
	mov eax, 0
	mov DWORD PTR [edi+32], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov eax, 1
	mov DWORD PTR [edi+40], eax
	mov esi, 30
296:
	sub esi, 1
	mov eax, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+16]
	mov ebx, edx
	and eax, 1
	mov ecx, 0
	sub ecx, eax
	shr edx, 31
	sub edx, 1
	and edx, ecx
	mov eax, ebx
	xor eax, edx
	sub eax, edx
	add eax, 2
	mov DWORD PTR [edi+16], eax
	mov ebx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [edi+24]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	shr eax, 1
	mov DWORD PTR [edi+20], ebx
	mov DWORD PTR [edi+24], eax
	mov ebx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+36]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+28], ebx
	mov DWORD PTR [edi+36], eax
	mov ebx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [edi+40]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+32], ebx
	mov DWORD PTR [edi+40], eax
	test esi, esi
	jne 296b
	mov eax, DWORD PTR [edi+28]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+32]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+36]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+40]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+172], eax
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
297:
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967280], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+24]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+28]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 297b
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967280], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967288]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+28]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967292]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+32]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967280], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
298:
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967284], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+24]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+28]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 298b
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967284], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967288]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+36]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967292]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+40]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967284], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov ebx, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [esi+12]
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add esi, eax
	mov eax, DWORD PTR [esi+8]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [esi+12]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+188], eax
	mov esi, DWORD PTR [edi+28]
	and esi, DWORD PTR [edi+184]
	mov eax, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+188]
	add esi, eax
	mov eax, DWORD PTR [edi+28]
	mul ebx
	mov ebp, eax
	mov eax, DWORD PTR [edi+32]
	mul ecx
	add ebp, eax
	mov eax, DWORD PTR [edi+44]
	mul ebp
	mov edx, esi
	sub edx, eax
	and edx, 1073741823
	sub esi, edx
	mov DWORD PTR [edi+192], esi
	mov esi, DWORD PTR [edi+36]
	and esi, DWORD PTR [edi+184]
	mov eax, DWORD PTR [edi+40]
	and eax, DWORD PTR [edi+188]
	add esi, eax
	mov eax, DWORD PTR [edi+36]
	mul ebx
	mov ebp, eax
	mov eax, DWORD PTR [edi+40]
	mul ecx
	add ebp, eax
	mov eax, DWORD PTR [edi+44]
	mul ebp
	mov edx, esi
	sub edx, eax
	and edx, 1073741823
	sub esi, edx
	mov DWORD PTR [edi+196], esi
	mov eax, DWORD PTR [edi+192]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+196]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+204], eax
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov DWORD PTR [edi+176], ebx
299:
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+200]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967276], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+28]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+32]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+32]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [esi+36]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+36]
	and eax, DWORD PTR [edi+200]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 40
	cmp esi, DWORD PTR [edi+180]
	jne 299b
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+200]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967276], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 20
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+28]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	mov eax, DWORD PTR [esi+4294967288]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+32]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967276], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov DWORD PTR [edi+176], ebx
2100:
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+204]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967280], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+28]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+32]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+32]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [esi+36]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+36]
	and eax, DWORD PTR [edi+204]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 40
	cmp esi, DWORD PTR [edi+180]
	jne 2100b
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+8]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+12]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+204]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967280], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 20
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+36]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	mov eax, DWORD PTR [esi+4294967288]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+40]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967280], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+100]
	sub esi, 1
	mov DWORD PTR [edi+100], esi
	test esi, esi
	jne 290b
	mov ebx, DWORD PTR [edi+64]
	add ebx, 16
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+24], eax
	mov eax, 1
	mov DWORD PTR [edi+28], eax
	mov eax, 0
	mov DWORD PTR [edi+32], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov eax, 1
	mov DWORD PTR [edi+40], eax
	mov esi, 30
2101:
	sub esi, 1
	mov eax, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+16]
	mov ebx, edx
	and eax, 1
	mov ecx, 0
	sub ecx, eax
	shr edx, 31
	sub edx, 1
	and edx, ecx
	mov eax, ebx
	xor eax, edx
	sub eax, edx
	add eax, 2
	mov DWORD PTR [edi+16], eax
	mov ebx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [edi+24]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	shr eax, 1
	mov DWORD PTR [edi+20], ebx
	mov DWORD PTR [edi+24], eax
	mov ebx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+36]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+28], ebx
	mov DWORD PTR [edi+36], eax
	mov ebx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [edi+40]
	mov ebp, ebx
	xor ebp, edx
	sub ebp, edx
	and ebp, ecx
	add eax, ebp
	mov ebp, eax
	and ebp, edx
	add ebx, ebp
	add ebx, ebx
	mov DWORD PTR [edi+32], ebx
	mov DWORD PTR [edi+40], eax
	test esi, esi
	jne 2101b
	mov eax, DWORD PTR [edi+28]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+32]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+36]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+40]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+172], eax
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
2102:
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+8], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 2102b
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+28]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+32]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967288], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
2103:
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967292], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+12], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 32
	cmp esi, DWORD PTR [edi+180]
	jne 2103b
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, ebp
	mov DWORD PTR [esi+4294967292], eax
	shr ebx, 30
	mov ebp, ebx
	mov ebx, ecx
	add ecx, ecx
	sbb ecx, ecx
	add esi, 16
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+36]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	mov eax, DWORD PTR [esi+4294967284]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+40]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebp
	mov DWORD PTR [esi+4294967292], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov ebx, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+4]
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add esi, eax
	mov eax, DWORD PTR [esi]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [esi+4]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+188], eax
	mov esi, DWORD PTR [edi+28]
	and esi, DWORD PTR [edi+184]
	mov eax, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+188]
	add esi, eax
	mov eax, DWORD PTR [edi+28]
	mul ebx
	mov ebp, eax
	mov eax, DWORD PTR [edi+32]
	mul ecx
	add ebp, eax
	mov eax, DWORD PTR [edi+44]
	mul ebp
	mov edx, esi
	sub edx, eax
	and edx, 1073741823
	sub esi, edx
	mov DWORD PTR [edi+192], esi
	mov esi, DWORD PTR [edi+36]
	and esi, DWORD PTR [edi+184]
	mov eax, DWORD PTR [edi+40]
	and eax, DWORD PTR [edi+188]
	add esi, eax
	mov eax, DWORD PTR [edi+36]
	mul ebx
	mov ebp, eax
	mov eax, DWORD PTR [edi+40]
	mul ecx
	add ebp, eax
	mov eax, DWORD PTR [edi+44]
	mul ebp
	mov edx, esi
	sub edx, eax
	and edx, 1073741823
	sub esi, edx
	mov DWORD PTR [edi+196], esi
	mov eax, DWORD PTR [edi+192]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+196]
	add eax, eax
	sbb eax, eax
	mov DWORD PTR [edi+204], eax
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov DWORD PTR [edi+176], ebx
2104:
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+200]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967284], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+24]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [esi+36]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+36]
	and eax, DWORD PTR [edi+200]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+8], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 40
	cmp esi, DWORD PTR [edi+180]
	jne 2104b
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+32]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+200]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967284], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 20
	mov eax, DWORD PTR [esi+4294967276]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+28]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+32]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967284], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov eax, DWORD PTR [edi+96]
	mov edx, eax
	add eax, eax
	add eax, eax
	add eax, edx
	add eax, esi
	mov DWORD PTR [edi+180], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov DWORD PTR [edi+176], ebx
2105:
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+204]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi+20]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+24]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [esi+36]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+36]
	and eax, DWORD PTR [edi+204]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+12], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 40
	cmp esi, DWORD PTR [edi+180]
	jne 2105b
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [esi]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+168]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [esi+4]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+172]
	sub ecx, eax
	sbb ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [esi+16]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+204]
	sub ecx, eax
	sbb ebp, 0
	mov eax, ebx
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967288], eax
	shr ebx, 30
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	add ebp, ebp
	sbb ebp, ebp
	add esi, 20
	mov eax, DWORD PTR [esi+4294967276]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+36]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	mov eax, DWORD PTR [esi+4294967280]
	add eax, eax
	sbb eax, eax
	and eax, DWORD PTR [edi+40]
	mov edx, eax
	add edx, edx
	sbb edx, edx
	sub ebx, eax
	sbb ecx, edx
	sbb ebp, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, DWORD PTR [edi+176]
	mov DWORD PTR [esi+4294967288], ebx
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov ebp, DWORD PTR [edi+92]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
2106:
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp], eax
	add ebp, 4
	add esi, 16
	sub ecx, 1
	jne 2106b
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov ebp, DWORD PTR [edi+76]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
2107:
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp], eax
	add ebp, 4
	add esi, 20
	sub ecx, 1
	jne 2107b
	mov ebp, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
2108:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2108b
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2109:
	cmp edx, 32
	jae 2110f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2111f
2110:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2111:
	cmp edx, 0
	jne 2109b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+76]
	mov edi, DWORD PTR [edi+96]
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2112f
	jmp 2113f
2112:
2114:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2114b
2113:
	and edi, 15
	jne 2115f
	jmp 2116f
2115:
2117:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2117b
2116:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+76]
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2118:
	cmp edx, 32
	jae 2119f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2120f
2119:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2120:
	cmp edx, 0
	jne 2118b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+76]
	mov edi, DWORD PTR [edi+96]
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2121f
	jmp 2122f
2121:
2123:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2123b
2122:
	and edi, 15
	jne 2124f
	jmp 2125f
2124:
2126:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2126b
2125:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+76]
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2127:
	cmp edx, 32
	jae 2128f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2129f
2128:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2129:
	cmp edx, 0
	jne 2127b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+76]
	mov edi, DWORD PTR [edi+96]
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2130f
	jmp 2131f
2130:
2132:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2132b
2131:
	and edi, 15
	jne 2133f
	jmp 2134f
2133:
2135:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2135b
2134:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+76]
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2136:
	cmp edx, 32
	jae 2137f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2138f
2137:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2138:
	cmp edx, 0
	jne 2136b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+76]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2139f
	jmp 2140f
2139:
2141:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2141b
2140:
	and edi, 15
	jne 2142f
	jmp 2143f
2142:
2144:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2144b
2143:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+56]
	mov ecx, DWORD PTR [edi+96]
	add ecx, ecx
	mov eax, 0
2145:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2145b
	mov ebp, DWORD PTR [edi+56]
	mov ebx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+56]
	mov ecx, 0
2146:
	cmp edx, 32
	jae 2147f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2148f
2147:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2148:
	cmp edx, 0
	jne 2146b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	xor ecx, -1
	mov ebp, DWORD PTR [edi+92]
	mov ebx, DWORD PTR [edi+56]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2149f
	jmp 2150f
2149:
2151:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2151b
2150:
	and edi, 15
	jne 2152f
	jmp 2153f
2152:
2154:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2154b
2153:
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	mov ecx, DWORD PTR [edi+96]
	add ecx, ecx
	mov eax, 0
2155:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2155b
	mov ecx, -1
	mov ebp, DWORD PTR [edi+76]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2156f
	jmp 2157f
2156:
2158:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2158b
2157:
	and edi, 15
	jne 2159f
	jmp 2160f
2159:
2161:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2161b
2160:
	mov edi, DWORD PTR [esp+60]
250:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2162:
	cmp edx, 32
	jae 2163f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2164f
2163:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2164:
	cmp edx, 0
	jne 2162b
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+112], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2165:
	cmp edx, 32
	jae 2166f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2167f
2166:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2167:
	cmp edx, 0
	jne 2165b
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+128], ebx
	mov eax, DWORD PTR [edi+116]
	and eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+132]
	and eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+132], eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2168f
	jmp 2169f
2168:
2170:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2170b
2169:
	and edi, 15
	jne 2171f
	jmp 2172f
2171:
2173:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2173b
2172:
	mov edi, DWORD PTR [esp+60]
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2174f
	jmp 2175f
2174:
2176:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2176b
2175:
	and edi, 15
	jne 2177f
	jmp 2178f
2177:
2179:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2179b
2178:
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	or ecx, 1
	xor ecx, 1
	mov DWORD PTR [eax], ecx
	mov eax, DWORD PTR [edi+144]
	cmp eax, 0
	je 2180f
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2182:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2182b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2183:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2184:
	cmp edx, 32
	jae 2185f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2186f
2185:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2186:
	cmp edx, 0
	jne 2184b
	mov edi, DWORD PTR [esp+60]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2187:
	cmp edx, 32
	jae 2188f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2189f
2188:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2189:
	cmp edx, 0
	jne 2187b
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2190:
	cmp edx, 32
	jae 2191f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2192f
2191:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2192:
	cmp edx, 0
	jne 2190b
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2193f
	jmp 2194f
2193:
2195:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2195b
2194:
	and edi, 15
	jne 2196f
	jmp 2197f
2196:
2198:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2198b
2197:
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
	jne 2183b
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2199f
	jmp 2200f
2199:
2201:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2201b
2200:
	and edi, 15
	jne 2202f
	jmp 2203f
2202:
2204:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2204b
2203:
	mov edi, DWORD PTR [esp+60]
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2205f
	jmp 2206f
2205:
2207:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2207b
2206:
	and edi, 15
	jne 2208f
	jmp 2209f
2208:
2210:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2210b
2209:
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	or ecx, 1
	xor ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2211:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2211b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2212:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2213:
	cmp edx, 32
	jae 2214f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2215f
2214:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2215:
	cmp edx, 0
	jne 2213b
	mov edi, DWORD PTR [esp+60]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2216:
	cmp edx, 32
	jae 2217f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2218f
2217:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2218:
	cmp edx, 0
	jne 2216b
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 4
	mov ecx, 0
2219:
	cmp edx, 32
	jae 2220f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2221f
2220:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2221:
	cmp edx, 0
	jne 2219b
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2222f
	jmp 2223f
2222:
2224:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2224b
2223:
	and edi, 15
	jne 2225f
	jmp 2226f
2225:
2227:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2227b
2226:
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
	jne 2212b
	jmp 2181f
2180:
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+40]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 8
	mov eax, DWORD PTR [ebx+4]
	or eax, -2147483648
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+88], eax
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2228:
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
	jne 2228b
	mov edi, DWORD PTR [esp+60]
	mov DWORD PTR [edi+64], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2229:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2229b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add esi, ecx
	mov ecx, DWORD PTR [esp+40]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	sub ecx, 4
	sub esi, ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+40]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	je 2230f
2232:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2232b
	jmp 2231f
2230:
2231:
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [esp+32]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 2
	mov ecx, DWORD PTR [esp+40]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	sub eax, ecx
	add eax, 1
	mov DWORD PTR [edi+72], eax
2233:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+92], eax
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+40]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+80], eax
	mov ebp, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+84], eax
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [edi+92]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+40]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
2234:
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
	jne 2234b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+40]
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
2235:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2235b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+40]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
2236:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2236b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2233b
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2237f
	jmp 2238f
2237:
2239:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2239b
2238:
	and edi, 15
	jne 2240f
	jmp 2241f
2240:
2242:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2242b
2241:
	mov edi, DWORD PTR [esp+60]
	mov ecx, -1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2243f
	jmp 2244f
2243:
2245:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2245b
2244:
	and edi, 15
	jne 2246f
	jmp 2247f
2246:
2248:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2248b
2247:
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	or ecx, 1
	xor ecx, 1
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+40]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 8
	mov eax, DWORD PTR [ebx+4]
	or eax, -2147483648
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+88], eax
	mov esi, DWORD PTR [edi+60]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
2249:
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
	jne 2249b
	mov edi, DWORD PTR [esp+60]
	mov DWORD PTR [edi+64], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 4
	mov eax, 0
2250:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2250b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add esi, ecx
	mov ecx, DWORD PTR [esp+40]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	sub ecx, 4
	sub esi, ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+40]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	je 2251f
2253:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2253b
	jmp 2252f
2251:
2252:
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [esp+32]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	shr eax, 2
	mov ecx, DWORD PTR [esp+40]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	shr ecx, 2
	sub eax, ecx
	add eax, 1
	mov DWORD PTR [edi+72], eax
2254:
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebx, eax
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+92], eax
	mov ecx, DWORD PTR [esp+32]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ebx, ecx
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	shr ecx, 1
	mov ecx, DWORD PTR [esp+40]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+80], eax
	mov ebp, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+84], eax
	mov ecx, DWORD PTR [edi+60]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+68], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+64]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+60]
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
	or ebx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+76], ebx
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [edi+88]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+60]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+80]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+84]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+60]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+76], ecx
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [edi+76]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [edi+92]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+40]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
2255:
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
	jne 2255b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+40]
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
2256:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2256b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+60]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+40]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
2257:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2257b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2254b
2181:
	mov ecx, DWORD PTR [edi+132]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2258f
	jmp 2259f
2258:
2260:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2260b
2259:
	and edi, 15
	jne 2261f
	jmp 2262f
2261:
2263:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2263b
2262:
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
2264:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2264b
	mov ecx, DWORD PTR [edi+132]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add ebx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2265f
	jmp 2266f
2265:
2267:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2267b
2266:
	and edi, 15
	jne 2268f
	jmp 2269f
2268:
2270:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2270b
2269:
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add esi, edx
	add edx, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add esi, ecx
	sub esi, 1
2271:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2271b
	mov ecx, DWORD PTR [edi+132]
	sub ecx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add edx, edx
	add ebp, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add edx, edx
	add ebx, edx
	shr edx, 1
	mov edi, DWORD PTR [esp+32]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2272f
	jmp 2273f
2272:
2274:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2274b
2273:
	and edi, 15
	jne 2275f
	jmp 2276f
2275:
2277:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2277b
2276:
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov esi, edi
	add esi, 160
	add esi, edx
	add edx, edx
	add esi, edx
	shr edx, 1
	add esi, ecx
	sub esi, 1
2278:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2278b
	mov eax, DWORD PTR [edi+132]
21:
	mov ebx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi+4]
	mov esi, DWORD PTR [edi+8]
	mov edi, DWORD PTR [edi+12]
	ret
	.p2align 6

vg_rsa_public_precompute:
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

vg_rsa_private_precompute:
	lea esp, [esp-96]
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+112]
	add eax, 7
	shr eax, 3
	add eax, eax
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+20], eax
	call {vg_rsa_public_precompute}
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+132]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+112]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+16], eax
	call {vg_rsa_private_precompute_primes}
	and eax, DWORD PTR [esp+80]
	and eax, 1
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+88], esi
	mov DWORD PTR [esp+92], ebp
	mov ebp, DWORD PTR [esp+112]
	add ebp, 7
	shr ebp, 3
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, DWORD PTR [esp+100]
	mov ecx, DWORD PTR [esp+112]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 32
	mov esi, DWORD PTR [esp+132]
	add esi, 3336
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	mov ecx, DWORD PTR [esp+120]
	add ecx, 7
	shr ecx, 3
	mov eax, ecx
	sub eax, 2
	shr eax, 31
	add ecx, eax
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
20:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 20b
	mov ebp, DWORD PTR [esp+112]
	add ebp, 7
	shr ebp, 3
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, DWORD PTR [esp+100]
	mov eax, DWORD PTR [esp+120]
	add eax, 7
	shr eax, 3
	mov ecx, eax
	sub ecx, 2
	shr ecx, 31
	add eax, ecx
	add eax, eax
	add eax, eax
	add eax, eax
	add ebp, eax
	mov ecx, DWORD PTR [esp+112]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, 32
	mov esi, DWORD PTR [esp+132]
	add esi, 3336
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	mov ecx, DWORD PTR [esp+128]
	add ecx, 7
	shr ecx, 3
	mov eax, ecx
	sub eax, 2
	shr eax, 31
	add ecx, eax
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
21:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 21b
	mov esi, DWORD PTR [esp+88]
	mov ebp, DWORD PTR [esp+92]
	mov eax, DWORD PTR [esp+80]
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [esp+84], ecx
	mov edx, DWORD PTR [esp+100]
	mov ecx, DWORD PTR [esp+104]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
22:
	movzx eax, BYTE PTR [edx]
	and eax, DWORD PTR [esp+84]
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	cmp ecx, 0
	jne 22b
	mov eax, DWORD PTR [esp+80]
	lea esp, [esp+96]
	ret
	.p2align 6
