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
	mov esi, DWORD PTR [esp+24]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, 8
	add esi, esi
	add esi, esi
	add esi, esi
	mov DWORD PTR [edi+148], esi
268:
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
	add edx, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+116], eax
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
	add edx, edx
	add eax, edx
	add edx, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+116]
	or eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+124]
	xor eax, 1
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, 1
	mov DWORD PTR [edi+128], eax
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
275:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 275b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+128]
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
	jne 276f
	jmp 277f
276:
278:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 278b
277:
	and edi, 15
	jne 279f
	jmp 280f
279:
281:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 281b
280:
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
288:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 288b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+124]
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
	jne 289f
	jmp 290f
289:
291:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 291b
290:
	and edi, 15
	jne 292f
	jmp 293f
292:
294:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 294b
293:
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
295:
	cmp edx, 32
	jae 296f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 297f
296:
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
297:
	cmp edx, 0
	jne 295b
	mov edi, DWORD PTR [esp+44]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+124]
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
	jne 298f
	jmp 299f
298:
2100:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2100b
299:
	and edi, 15
	jne 2101f
	jmp 2102f
2101:
2103:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2103b
2102:
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+148]
	sub eax, 1
	mov DWORD PTR [edi+148], eax
	jne 268b
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
	jne 2104f
	jmp 2105f
2104:
2106:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2106b
2105:
	and edi, 15
	jne 2107f
	jmp 2108f
2107:
2109:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2109b
2108:
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
	jne 2110f
	jmp 2111f
2110:
2112:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2112b
2111:
	and edi, 15
	jne 2113f
	jmp 2114f
2113:
2115:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2115b
2114:
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
	mov ebp, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
2116:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2116b
	mov ecx, -1
	mov ebp, DWORD PTR [edi+64]
	mov ebx, DWORD PTR [edi+84]
	mov edi, DWORD PTR [edi+96]
	sub edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2117f
	jmp 2118f
2117:
2119:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2119b
2118:
	and edi, 15
	jne 2120f
	jmp 2121f
2120:
2122:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2122b
2121:
	mov edi, DWORD PTR [esp+44]
	mov ecx, -1
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+64]
	mov edi, DWORD PTR [edi+96]
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2123f
	jmp 2124f
2123:
2125:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2125b
2124:
	and edi, 15
	jne 2126f
	jmp 2127f
2126:
2128:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2128b
2127:
	mov edi, DWORD PTR [esp+44]
	mov ebp, DWORD PTR [edi+68]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
2129:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2129b
	mov ecx, -1
	mov ebp, DWORD PTR [edi+52]
	mov ebx, DWORD PTR [edi+68]
	mov edi, DWORD PTR [edi+96]
	sub edi, 4
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
	mov edi, DWORD PTR [esp+44]
	mov ebp, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
2136:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2136b
	mov ecx, DWORD PTR [edi+160]
	and ecx, 1
	sub ecx, 1
	mov ebp, DWORD PTR [edi+64]
	mov ebx, DWORD PTR [edi+84]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
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
	mov ebp, DWORD PTR [edi+68]
	mov ebx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+68]
	mov ecx, 0
2143:
	cmp edx, 32
	jae 2144f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2145f
2144:
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
2145:
	cmp edx, 0
	jne 2143b
	mov edi, DWORD PTR [esp+44]
	mov eax, 1
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+96]
	add eax, 4
	shr eax, 2
	mov ecx, eax
	add eax, ecx
	add eax, ecx
	mov DWORD PTR [edi+100], eax
2146:
	mov ebx, DWORD PTR [edi+64]
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+20], eax
	mov ebx, DWORD PTR [edi+68]
	mov eax, DWORD PTR [ebx]
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
2147:
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
	jne 2147b
	mov ecx, DWORD PTR [edi+28]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 4
	mov edi, DWORD PTR [edi+64]
	mov ebx, 0
2148:
	cmp esi, 16
	jae 2149f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2150f
2149:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2150:
	cmp esi, 0
	jne 2148b
	mov DWORD PTR [ebp], ebx
	mov eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 4
	mov edi, DWORD PTR [edi+68]
	mov ebx, 0
2151:
	cmp esi, 16
	jae 2152f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2153f
2152:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+4]
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+8]
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+12]
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2153:
	cmp esi, 0
	jne 2151b
	mov eax, DWORD PTR [ebp]
	add eax, ebx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+44]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2154:
	cmp edx, 32
	jae 2155f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2156f
2155:
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
2156:
	cmp edx, 0
	jne 2154b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+28]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2157f
	jmp 2158f
2157:
2159:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2159b
2158:
	and edi, 15
	jne 2160f
	jmp 2161f
2160:
2162:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2162b
2161:
	mov edi, DWORD PTR [esp+44]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2163:
	cmp edx, 32
	jae 2164f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2165f
2164:
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
2165:
	cmp edx, 0
	jne 2163b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+32]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
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
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	sub esi, 4
	mov edi, DWORD PTR [edi+52]
2172:
	mov eax, DWORD PTR [ebp]
	mov ebx, DWORD PTR [ebp+4]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+8]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+4], eax
	add ebp, 8
	add edi, 8
	sub esi, 8
	jne 2172b
	mov eax, DWORD PTR [ebp]
	mov ebx, DWORD PTR [ebp+4]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	add ebp, 4
	add edi, 4
	mov eax, DWORD PTR [ebp]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [ebp]
	mov ebx, ecx
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	mov edi, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [edi+36]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 4
	mov edi, DWORD PTR [edi+64]
	mov ebx, 0
2173:
	cmp esi, 16
	jae 2174f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2175f
2174:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2175:
	cmp esi, 0
	jne 2173b
	mov DWORD PTR [ebp], ebx
	mov eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [edi+40]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 4
	mov edi, DWORD PTR [edi+68]
	mov ebx, 0
2176:
	cmp esi, 16
	jae 2177f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2178f
2177:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+4]
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+8]
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+12]
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2178:
	cmp esi, 0
	jne 2176b
	mov eax, DWORD PTR [ebp]
	add eax, ebx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+44]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2179:
	cmp edx, 32
	jae 2180f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2181f
2180:
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
2181:
	cmp edx, 0
	jne 2179b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+36]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2182f
	jmp 2183f
2182:
2184:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2184b
2183:
	and edi, 15
	jne 2185f
	jmp 2186f
2185:
2187:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2187b
2186:
	mov edi, DWORD PTR [esp+44]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2188:
	cmp edx, 32
	jae 2189f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2190f
2189:
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
2190:
	cmp edx, 0
	jne 2188b
	mov edi, DWORD PTR [esp+44]
	mov eax, DWORD PTR [edi+40]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2191f
	jmp 2192f
2191:
2193:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2193b
2192:
	and edi, 15
	jne 2194f
	jmp 2195f
2194:
2196:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2196b
2195:
	mov edi, DWORD PTR [esp+44]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	sub esi, 4
	mov edi, DWORD PTR [edi+68]
2197:
	mov eax, DWORD PTR [ebp]
	mov ebx, DWORD PTR [ebp+4]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+8]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+4], eax
	add ebp, 8
	add edi, 8
	sub esi, 8
	jne 2197b
	mov eax, DWORD PTR [ebp]
	mov ebx, DWORD PTR [ebp+4]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	add ebp, 4
	add edi, 4
	mov eax, DWORD PTR [ebp]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [ebp]
	mov ebx, ecx
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	mov edi, DWORD PTR [esp+44]
	mov ecx, -1
	mov ebp, DWORD PTR [edi+52]
	mov ebx, DWORD PTR [edi+64]
	mov edi, DWORD PTR [edi+96]
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2198f
	jmp 2199f
2198:
2200:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2200b
2199:
	and edi, 15
	jne 2201f
	jmp 2202f
2201:
2203:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2203b
2202:
	mov edi, DWORD PTR [esp+44]
	mov esi, DWORD PTR [edi+100]
	sub esi, 1
	mov DWORD PTR [edi+100], esi
	test esi, esi
	jne 2146b
	mov ebp, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 0
	mov eax, 0
2204:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2204b
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2205:
	cmp edx, 32
	jae 2206f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2207:
	cmp edx, 0
	jne 2205b
	mov edi, DWORD PTR [esp+44]
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	xor ecx, -1
	mov ebp, DWORD PTR [edi+64]
	mov ebx, DWORD PTR [edi+84]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2208f
	jmp 2209f
2208:
2210:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2210b
2209:
	and edi, 15
	jne 2211f
	jmp 2212f
2211:
2213:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2213b
2212:
	mov edi, DWORD PTR [esp+44]
	mov ecx, -1
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+52]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2214f
	jmp 2215f
2214:
2216:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2216b
2215:
	and edi, 15
	jne 2217f
	jmp 2218f
2217:
2219:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2219b
2218:
	mov edi, DWORD PTR [esp+44]
	mov ebp, DWORD PTR [edi+68]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 0
	mov eax, 0
2220:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
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
2221:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2221b
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
2222:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2222b
	mov esi, DWORD PTR [esp+24]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, 8
	add esi, esi
	add esi, esi
	add esi, esi
	mov DWORD PTR [edi+148], esi
2223:
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
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+116], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+116]
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
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2224f
	jmp 2225f
2224:
2226:
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
	jne 2226b
2225:
	and edx, 15
	jne 2227f
	jmp 2228f
2227:
2229:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2229b
2228:
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
	mov ecx, 0
2230:
	cmp edx, 32
	jae 2231f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2232f
2231:
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
2232:
	cmp edx, 0
	jne 2230b
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
2233:
	cmp edx, 32
	jae 2234f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2235f
2234:
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
2235:
	cmp edx, 0
	jne 2233b
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
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
2236:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2236b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+148]
	sub eax, 1
	mov DWORD PTR [edi+148], eax
	jne 2223b
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
2237:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2237b
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
	jne 2238f
	jmp 2239f
2238:
2240:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2240b
2239:
	and edi, 15
	jne 2241f
	jmp 2242f
2241:
2243:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2243b
2242:
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
2244:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2244b
	mov esi, DWORD PTR [esp+24]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, 24
	add esi, esi
	add esi, esi
	add esi, esi
2245:
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
	mov ecx, 0
2246:
	cmp edx, 32
	jae 2247f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2248f
2247:
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
2248:
	cmp edx, 0
	jne 2246b
	mov edi, DWORD PTR [esp+44]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
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
	add edx, 4
	mov ecx, 0
2249:
	cmp edx, 32
	jae 2250f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2251f
2250:
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
2251:
	cmp edx, 0
	jne 2249b
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
	add ecx, DWORD PTR [edi+136]
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
	add edx, 4
	mov ecx, 0
2252:
	cmp edx, 32
	jae 2253f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2254f
2253:
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
2254:
	cmp edx, 0
	jne 2252b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
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
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2255f
	jmp 2256f
2255:
2257:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2257b
2256:
	and edi, 15
	jne 2258f
	jmp 2259f
2258:
2260:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2260b
2259:
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
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+140]
	mov DWORD PTR [eax], ecx
	sub esi, 1
	cmp esi, 0
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
2261:
	cmp edx, 32
	jae 2262f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2263f
2262:
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
2263:
	cmp edx, 0
	jne 2261b
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
	jne 2264f
	jmp 2265f
2264:
2266:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2266b
2265:
	and edi, 15
	jne 2267f
	jmp 2268f
2267:
2269:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2269b
2268:
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
2270:
	cmp edx, 32
	jae 2271f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2272f
2271:
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
2272:
	cmp edx, 0
	jne 2270b
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
2273:
	cmp edx, 32
	jae 2274f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2275f
2274:
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
2275:
	cmp edx, 0
	jne 2273b
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
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	shr edx, 1
	add eax, edx
	sub eax, 8
	mov ecx, 0
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
	add ebp, edx
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
2276:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2276b
	mov esi, DWORD PTR [esp+24]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, 8
	add esi, esi
	add esi, esi
	add esi, esi
2277:
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
	add ebx, edx
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
2278:
	cmp edx, 32
	jae 2279f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2280f
2279:
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
2280:
	cmp edx, 0
	jne 2278b
	mov edi, DWORD PTR [esp+44]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+136], eax
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
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	add edx, 4
	mov ecx, 0
2281:
	cmp edx, 32
	jae 2282f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2283f
2282:
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
2283:
	cmp edx, 0
	jne 2281b
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
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+136]
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
	add ebp, edx
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
	add edx, edx
	add edi, edx
	add edx, edx
	add edx, edx
	add edi, edx
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
	add edx, 4
	mov ecx, 0
2284:
	cmp edx, 32
	jae 2285f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2286f
2285:
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
2286:
	cmp edx, 0
	jne 2284b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	xor ebx, -1
	and ebx, 1
	xor ecx, -1
	mov DWORD PTR [edi+140], ebx
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
	shr edx, 1
	mov edi, DWORD PTR [esp+24]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, 8
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2287f
	jmp 2288f
2287:
2289:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2289b
2288:
	and edi, 15
	jne 2290f
	jmp 2291f
2290:
2292:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2292b
2291:
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
	add eax, edx
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
	jne 2277b
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
2293:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 2293b
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
2294:
	cmp edx, 32
	jae 2295f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
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
2296:
	cmp edx, 0
	jne 2294b
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
	jne 2297f
	jmp 2298f
2297:
2299:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2299b
2298:
	and edi, 15
	jne 2300f
	jmp 2301f
2300:
2302:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2302b
2301:
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
2303:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2303b
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
	add ebx, edx
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
	jne 2304f
	jmp 2305f
2304:
2306:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2306b
2305:
	and edi, 15
	jne 2307f
	jmp 2308f
2307:
2309:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2309b
2308:
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
2310:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2310b
	mov esi, DWORD PTR [esp+24]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, 8
	add esi, esi
	add esi, esi
	add esi, esi
	mov DWORD PTR [edi+148], esi
2311:
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
	add edx, edx
	add eax, edx
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	shr edx, 1
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+116], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+116]
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
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2312f
	jmp 2313f
2312:
2314:
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
	jne 2314b
2313:
	and edx, 15
	jne 2315f
	jmp 2316f
2315:
2317:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2317b
2316:
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
	mov ecx, 0
2318:
	cmp edx, 32
	jae 2319f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2320f
2319:
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
2320:
	cmp edx, 0
	jne 2318b
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
	add edi, edx
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
2321:
	cmp edx, 32
	jae 2322f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2323f
2322:
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
2323:
	cmp edx, 0
	jne 2321b
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
2324:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2324b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+148]
	sub eax, 1
	mov DWORD PTR [edi+148], eax
	jne 2311b
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
2325:
	cmp edx, 32
	jae 2326f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2327f
2326:
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
2327:
	cmp edx, 0
	jne 2325b
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
2328:
	cmp edx, 32
	jae 2329f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2330f
2329:
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
2330:
	cmp edx, 0
	jne 2328b
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
2331:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2331b
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
2332:
	cmp edx, 32
	jae 2333f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2334f
2333:
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
2334:
	cmp edx, 0
	jne 2332b
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
2335:
	cmp edx, 32
	jae 2336f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2337f
2336:
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
2337:
	cmp edx, 0
	jne 2335b
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
	jne 2338f
	jmp 2339f
2338:
2340:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2340b
2339:
	and edi, 15
	jne 2341f
	jmp 2342f
2341:
2343:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2343b
2342:
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
	jne 2344f
	jmp 2345f
2344:
2346:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2346b
2345:
	and edi, 15
	jne 2347f
	jmp 2348f
2347:
2349:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2349b
2348:
	mov edi, DWORD PTR [esp+44]
	mov esi, DWORD PTR [esp+24]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, 24
	add esi, esi
	add esi, esi
	add esi, esi
	shr esi, 1
	mov DWORD PTR [edi+148], esi
2350:
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
2351:
	cmp edx, 32
	jae 2352f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2353f
2352:
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
2353:
	cmp edx, 0
	jne 2351b
	mov edi, DWORD PTR [esp+44]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+36], eax
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
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, 0
2354:
	cmp edx, 32
	jae 2355f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2356f
2355:
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
2356:
	cmp edx, 0
	jne 2354b
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
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+36]
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
2357:
	cmp edx, 32
	jae 2358f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2359f
2358:
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
2359:
	cmp edx, 0
	jne 2357b
	mov edi, DWORD PTR [esp+44]
	mov eax, ecx
	and eax, 1
	mov DWORD PTR [edi+40], eax
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
	shr edx, 1
	mov edx, DWORD PTR [esp+24]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ecx, 0
2360:
	cmp edx, 32
	jae 2361f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2362f
2361:
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
2362:
	cmp edx, 0
	jne 2360b
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
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+40]
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
2363:
	cmp edx, 32
	jae 2364f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2365f
2364:
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
2365:
	cmp edx, 0
	jne 2363b
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
2366:
	cmp edx, 32
	jae 2367f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2368f
2367:
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
2368:
	cmp edx, 0
	jne 2366b
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
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	or ecx, 1
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
	add ebp, edx
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
2369:
	cmp edx, 32
	jae 2370f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2371f
2370:
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
2371:
	cmp edx, 0
	jne 2369b
	mov edi, DWORD PTR [esp+44]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+44], ebx
	mov eax, DWORD PTR [edi+44]
	xor eax, 1
	mov DWORD PTR [edi+48], eax
	mov ecx, DWORD PTR [edi+44]
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
	jne 2372f
	jmp 2373f
2372:
2374:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2374b
2373:
	and edi, 15
	jne 2375f
	jmp 2376f
2375:
2377:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2377b
2376:
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
2378:
	cmp edx, 32
	jae 2379f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2380f
2379:
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
2380:
	cmp edx, 0
	jne 2378b
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
	add edx, edx
	add eax, edx
	shr edx, 1
	shr edx, 1
	mov ecx, DWORD PTR [eax]
	add ecx, DWORD PTR [edi+48]
	mov DWORD PTR [eax], ecx
	mov eax, DWORD PTR [edi+148]
	sub eax, 1
	mov DWORD PTR [edi+148], eax
	jne 2350b
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
2381:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 2381b
	mov eax, 0
	sub eax, ecx
	or eax, ecx
	shr eax, 31
	xor eax, 1
	mov DWORD PTR [edi+52], eax
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
2382:
	cmp edx, 32
	jae 2383f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2384f
2383:
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
2384:
	cmp edx, 0
	jne 2382b
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
2385:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2385b
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
2386:
	cmp edx, 32
	jae 2387f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2388f
2387:
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
2388:
	cmp edx, 0
	jne 2386b
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
2389:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2389b
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
	jne 2390f
	jmp 2391f
2390:
2392:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2392b
2391:
	and edi, 15
	jne 2393f
	jmp 2394f
2393:
2395:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2395b
2394:
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
2396:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2396b
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
	jne 2397f
	jmp 2398f
2397:
2399:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2399b
2398:
	and edi, 15
	jne 2400f
	jmp 2401f
2400:
2402:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2402b
2401:
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
2403:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2403b
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
	jne 220f
	jmp 221f
220:
222:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 222b
221:
	and edi, 15
	jne 223f
	jmp 224f
223:
225:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 225b
224:
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
	jne 226f
	jmp 227f
226:
228:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 228b
227:
	and edi, 15
	jne 229f
	jmp 230f
229:
231:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 231b
230:
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
232:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 232b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
233:
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
234:
	cmp edx, 32
	jae 235f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 236f
235:
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
236:
	cmp edx, 0
	jne 234b
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
237:
	cmp edx, 32
	jae 238f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 239f
238:
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
239:
	cmp edx, 0
	jne 237b
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
	jne 243f
	jmp 244f
243:
245:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 245b
244:
	and edi, 15
	jne 246f
	jmp 247f
246:
248:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 248b
247:
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
	jne 233b
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
	add ebx, edx
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
249:
	cmp edx, 32
	jae 250f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 251f
250:
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
251:
	cmp edx, 0
	jne 249b
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
252:
	cmp edx, 32
	jae 253f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 254f
253:
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
254:
	cmp edx, 0
	jne 252b
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
255:
	cmp edx, 32
	jae 256f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 257f
256:
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
257:
	cmp edx, 0
	jne 255b
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
	jne 267f
	jmp 268f
267:
269:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 269b
268:
	and edi, 15
	jne 270f
	jmp 271f
270:
272:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 272b
271:
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
	mov esi, 3
273:
	cmp esi, 3
	je 274f
	cmp esi, 2
	je 276f
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
	jne 278f
	jmp 279f
278:
280:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 280b
279:
	and edi, 15
	jne 281f
	jmp 282f
281:
283:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 283b
282:
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
	jne 284f
	jmp 285f
284:
286:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 286b
285:
	and edi, 15
	jne 287f
	jmp 288f
287:
289:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 289b
288:
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
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+40]
	ror eax, 13
	add esi, eax
	jmp 277f
276:
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
	jne 296f
	jmp 297f
296:
298:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 298b
297:
	and edi, 15
	jne 299f
	jmp 2100f
299:
2101:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2101b
2100:
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
	jne 2102f
	jmp 2103f
2102:
2104:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2104b
2103:
	and edi, 15
	jne 2105f
	jmp 2106f
2105:
2107:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2107b
2106:
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
	add esi, 2162688
277:
	jmp 275f
274:
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
	jne 2114f
	jmp 2115f
2114:
2116:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2116b
2115:
	and edi, 15
	jne 2117f
	jmp 2118f
2117:
2119:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2119b
2118:
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
	jne 2120f
	jmp 2121f
2120:
2122:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2122b
2121:
	and edi, 15
	jne 2123f
	jmp 2124f
2123:
2125:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2125b
2124:
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
	jne 2126f
	jmp 2127f
2126:
2128:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2128b
2127:
	and edi, 15
	jne 2129f
	jmp 2130f
2129:
2131:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2131b
2130:
	mov edi, DWORD PTR [esp+68]
	add esi, 2162688
275:
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
2132:
	cmp edx, 32
	jae 2133f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2134f
2133:
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
2134:
	cmp edx, 0
	jne 2132b
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
	jne 2135f
	jmp 2136f
2135:
2137:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2137b
2136:
	and edi, 15
	jne 2138f
	jmp 2139f
2138:
2140:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2140b
2139:
	mov edi, DWORD PTR [esp+68]
2141:
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
	jne 2142f
	jmp 2143f
2142:
2144:
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
	jne 2144b
2143:
	and edx, 15
	jne 2145f
	jmp 2146f
2145:
2147:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2147b
2146:
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
2148:
	cmp edx, 32
	jae 2149f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2150f
2149:
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
2150:
	cmp edx, 0
	jne 2148b
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
2151:
	cmp edx, 32
	jae 2152f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2153f
2152:
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
2153:
	cmp edx, 0
	jne 2151b
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
2154:
	cmp edx, 32
	jae 2155f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2156f
2155:
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
2156:
	cmp edx, 0
	jne 2154b
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
	jne 2157f
	jmp 2158f
2157:
2159:
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
	jne 2159b
2158:
	and edx, 15
	jne 2160f
	jmp 2161f
2160:
2162:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2162b
2161:
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
2163:
	cmp edx, 32
	jae 2164f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2165f
2164:
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
2165:
	cmp edx, 0
	jne 2163b
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
2166:
	cmp edx, 32
	jae 2167f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2168f
2167:
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
2168:
	cmp edx, 0
	jne 2166b
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
2169:
	cmp edx, 32
	jae 2170f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2171f
2170:
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
2171:
	cmp edx, 0
	jne 2169b
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
	jne 2172f
	jmp 2173f
2172:
2174:
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
	jne 2174b
2173:
	and edx, 15
	jne 2175f
	jmp 2176f
2175:
2177:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2177b
2176:
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
2178:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2178b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	sub esi, 65536
	cmp esi, 65536
	jae 2141b
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
2179:
	cmp edx, 32
	jae 2180f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2181f
2180:
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
2181:
	cmp edx, 0
	jne 2179b
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
2182:
	cmp edx, 32
	jae 2183f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2184f
2183:
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
2184:
	cmp edx, 0
	jne 2182b
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
	jne 273b
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
2185:
	cmp edx, 32
	jae 2186f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2187f
2186:
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
2187:
	cmp edx, 0
	jne 2185b
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
	jne 2188f
	jmp 2189f
2188:
2190:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2190b
2189:
	and edi, 15
	jne 2191f
	jmp 2192f
2191:
2193:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2193b
2192:
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
	jne 2194f
	jmp 2195f
2194:
2196:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2196b
2195:
	and edi, 15
	jne 2197f
	jmp 2198f
2197:
2199:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2199b
2198:
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
2200:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2200b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2201:
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
2202:
	cmp edx, 32
	jae 2203f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2204f
2203:
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
2204:
	cmp edx, 0
	jne 2202b
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
2208:
	cmp edx, 32
	jae 2209f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2210f
2209:
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
2210:
	cmp edx, 0
	jne 2208b
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
	jne 2211f
	jmp 2212f
2211:
2213:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2213b
2212:
	and edi, 15
	jne 2214f
	jmp 2215f
2214:
2216:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2216b
2215:
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
	jne 2201b
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
2217:
	cmp edx, 32
	jae 2218f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2219f
2218:
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
2219:
	cmp edx, 0
	jne 2217b
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
2220:
	cmp edx, 32
	jae 2221f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2222f
2221:
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
2222:
	cmp edx, 0
	jne 2220b
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
	jne 2223f
	jmp 2224f
2223:
2225:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2225b
2224:
	and edi, 15
	jne 2226f
	jmp 2227f
2226:
2228:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2228b
2227:
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
	jne 2229f
	jmp 2230f
2229:
2231:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2231b
2230:
	and edi, 15
	jne 2232f
	jmp 2233f
2232:
2234:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2234b
2233:
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
2235:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2235b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2236:
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
2237:
	cmp edx, 32
	jae 2238f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2239f
2238:
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
2239:
	cmp edx, 0
	jne 2237b
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
2240:
	cmp edx, 32
	jae 2241f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2242f
2241:
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
2242:
	cmp edx, 0
	jne 2240b
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
2243:
	cmp edx, 32
	jae 2244f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2245f
2244:
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
2245:
	cmp edx, 0
	jne 2243b
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
	jne 2246f
	jmp 2247f
2246:
2248:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2248b
2247:
	and edi, 15
	jne 2249f
	jmp 2250f
2249:
2251:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2251b
2250:
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
	jne 2236b
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
2252:
	cmp edx, 32
	jae 2253f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2254f
2253:
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
2254:
	cmp edx, 0
	jne 2252b
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
2255:
	cmp edx, 32
	jae 2256f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2257f
2256:
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
2257:
	cmp edx, 0
	jne 2255b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
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
	jne 210f
	jmp 211f
210:
212:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 212b
211:
	and edi, 15
	jne 213f
	jmp 214f
213:
215:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 215b
214:
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
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
217:
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
218:
	cmp edx, 32
	jae 219f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
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
220:
	cmp edx, 0
	jne 218b
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
221:
	cmp edx, 32
	jae 222f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
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
223:
	cmp edx, 0
	jne 221b
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
224:
	cmp edx, 32
	jae 225f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 226f
225:
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
226:
	cmp edx, 0
	jne 224b
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
	jne 227f
	jmp 228f
227:
229:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 229b
228:
	and edi, 15
	jne 230f
	jmp 231f
230:
232:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 232b
231:
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
	jne 217b
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
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+120], ebx
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
239:
	cmp edx, 32
	jae 240f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 241f
240:
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
241:
	cmp edx, 0
	jne 239b
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
242:
	cmp edx, 32
	jae 243f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 244f
243:
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
244:
	cmp edx, 0
	jne 242b
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+124], ebx
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
	jne 245f
	jmp 246f
245:
247:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 247b
246:
	and edi, 15
	jne 248f
	jmp 249f
248:
250:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 250b
249:
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
263:
	cmp edx, 32
	jae 264f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 265f
264:
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
265:
	cmp edx, 0
	jne 263b
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [esp+32]
	and eax, 15
	je 266f
	cmp eax, eax
	jmp 267f
266:
	mov eax, DWORD PTR [esp+32]
	cmp eax, 128
	jae 268f
	cmp eax, eax
	jmp 269f
268:
	mov eax, DWORD PTR [esp+32]
	shr eax, 1
	add eax, 1
	mov ecx, DWORD PTR [esp+40]
	cmp ecx, eax
	jb 270f
	cmp eax, eax
	jmp 271f
270:
	mov ecx, DWORD PTR [esp+48]
	cmp ecx, eax
271:
269:
267:
	jb 272f
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
274:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 274b
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
281:
	cmp edx, 32
	jae 282f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
283:
	cmp edx, 0
	jne 281b
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
	jmp 273f
272:
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
	jne 284f
	jmp 285f
284:
286:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 286b
285:
	and edi, 15
	jne 287f
	jmp 288f
287:
289:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 289b
288:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+60]
	mov eax, DWORD PTR [ebp]
	xor eax, 1
	mov ebx, ebp
	add ebx, 4
	mov esi, DWORD PTR [edi+96]
	sub esi, 4
290:
	or eax, DWORD PTR [ebx]
	add ebx, 4
	sub esi, 4
	jne 290b
	sub eax, 1
	sbb eax, eax
	and eax, 2
	mov ecx, DWORD PTR [ebp]
	or ecx, eax
	mov DWORD PTR [ebp], ecx
	mov ecx, -1
	mov ebp, DWORD PTR [edi+60]
	mov ebx, DWORD PTR [edi+64]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 291f
	jmp 292f
291:
293:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 293b
292:
	and edi, 15
	jne 294f
	jmp 295f
294:
296:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 296b
295:
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov ecx, -1
	mov ebp, DWORD PTR [edi+52]
	mov ebx, DWORD PTR [edi+68]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 297f
	jmp 298f
297:
299:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 299b
298:
	and edi, 15
	jne 2100f
	jmp 2101f
2100:
2102:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2102b
2101:
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov ebp, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
2103:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2103b
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
	jne 2104f
	jmp 2105f
2104:
2106:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2106b
2105:
	and edi, 15
	jne 2107f
	jmp 2108f
2107:
2109:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2109b
2108:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+68]
	mov ebx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+68]
	mov ecx, 0
2110:
	cmp edx, 32
	jae 2111f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2112f
2111:
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
2112:
	cmp edx, 0
	jne 2110b
	mov edi, DWORD PTR [esp+60]
	mov eax, 1
	mov DWORD PTR [edi+16], eax
	mov ebp, DWORD PTR [edi+72]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
2113:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2113b
	mov ebp, DWORD PTR [edi+76]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
2114:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2114b
	mov eax, DWORD PTR [edi+76]
	mov ecx, 1
	mov DWORD PTR [eax], ecx
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
	add eax, 4
	shr eax, 2
	mov ecx, eax
	add eax, ecx
	add eax, ecx
	mov DWORD PTR [edi+100], eax
2115:
	mov ebx, DWORD PTR [edi+64]
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+20], eax
	mov ebx, DWORD PTR [edi+68]
	mov eax, DWORD PTR [ebx]
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
2116:
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
	jne 2116b
	mov ecx, DWORD PTR [edi+28]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 4
	mov edi, DWORD PTR [edi+64]
	mov ebx, 0
2117:
	cmp esi, 16
	jae 2118f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2119f
2118:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2119:
	cmp esi, 0
	jne 2117b
	mov DWORD PTR [ebp], ebx
	mov eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 4
	mov edi, DWORD PTR [edi+68]
	mov ebx, 0
2120:
	cmp esi, 16
	jae 2121f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2122f
2121:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+4]
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+8]
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+12]
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2122:
	cmp esi, 0
	jne 2120b
	mov eax, DWORD PTR [ebp]
	add eax, ebx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2123:
	cmp edx, 32
	jae 2124f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2125f
2124:
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
2125:
	cmp edx, 0
	jne 2123b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+28]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2126f
	jmp 2127f
2126:
2128:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2128b
2127:
	and edi, 15
	jne 2129f
	jmp 2130f
2129:
2131:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2131b
2130:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2132:
	cmp edx, 32
	jae 2133f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2134f
2133:
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
2134:
	cmp edx, 0
	jne 2132b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+32]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2135f
	jmp 2136f
2135:
2137:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2137b
2136:
	and edi, 15
	jne 2138f
	jmp 2139f
2138:
2140:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2140b
2139:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 0
	mov edi, DWORD PTR [edi+52]
2141:
	mov eax, DWORD PTR [ebp]
	mov ebx, DWORD PTR [ebp+4]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+8]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+4], eax
	add ebp, 8
	add edi, 8
	sub esi, 8
	jne 2141b
	mov eax, DWORD PTR [ebp]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [ebp]
	mov ebx, ecx
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	mov edi, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [edi+36]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 4
	mov edi, DWORD PTR [edi+64]
	mov ebx, 0
2142:
	cmp esi, 16
	jae 2143f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2144f
2143:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2144:
	cmp esi, 0
	jne 2142b
	mov DWORD PTR [ebp], ebx
	mov eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [edi+40]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 4
	mov edi, DWORD PTR [edi+68]
	mov ebx, 0
2145:
	cmp esi, 16
	jae 2146f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2147f
2146:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+4]
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+8]
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+12]
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2147:
	cmp esi, 0
	jne 2145b
	mov eax, DWORD PTR [ebp]
	add eax, ebx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2148:
	cmp edx, 32
	jae 2149f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2150f
2149:
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
2150:
	cmp edx, 0
	jne 2148b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+36]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2151f
	jmp 2152f
2151:
2153:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2153b
2152:
	and edi, 15
	jne 2154f
	jmp 2155f
2154:
2156:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2156b
2155:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2157:
	cmp edx, 32
	jae 2158f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2159f
2158:
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
2159:
	cmp edx, 0
	jne 2157b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+40]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2160f
	jmp 2161f
2160:
2162:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2162b
2161:
	and edi, 15
	jne 2163f
	jmp 2164f
2163:
2165:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2165b
2164:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 0
	mov edi, DWORD PTR [edi+56]
2166:
	mov eax, DWORD PTR [ebp]
	mov ebx, DWORD PTR [ebp+4]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+8]
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi+4], eax
	add ebp, 8
	add edi, 8
	sub esi, 8
	jne 2166b
	mov eax, DWORD PTR [ebp]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [ebp]
	mov ebx, ecx
	shr eax, 30
	add ebx, ebx
	add ebx, ebx
	add eax, ebx
	mov DWORD PTR [edi], eax
	mov edi, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [edi+28]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 0
	mov edi, DWORD PTR [edi+72]
	mov ebx, 0
2167:
	cmp esi, 16
	jae 2168f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2169f
2168:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2169:
	cmp esi, 0
	jne 2167b
	mov DWORD PTR [ebp], ebx
	mov eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 0
	mov edi, DWORD PTR [edi+76]
	mov ebx, 0
2170:
	cmp esi, 16
	jae 2171f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2172f
2171:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+4]
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+8]
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+12]
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2172:
	cmp esi, 0
	jne 2170b
	mov eax, DWORD PTR [ebp]
	add eax, ebx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2173:
	cmp edx, 32
	jae 2174f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2175f
2174:
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
2175:
	cmp edx, 0
	jne 2173b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+28]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2176f
	jmp 2177f
2176:
2178:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2178b
2177:
	and edi, 15
	jne 2179f
	jmp 2180f
2179:
2181:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2181b
2180:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2182:
	cmp edx, 32
	jae 2183f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2184f
2183:
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
2184:
	cmp edx, 0
	jne 2182b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+32]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
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
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov esi, ecx
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	add ebx, 4
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov ebx, DWORD PTR [edi+80]
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [edi+44]
	mul ecx
	mov ecx, eax
	mov DWORD PTR [edi+48], esi
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 0
	mov edi, DWORD PTR [edi+60]
	mov ebx, 0
2191:
	cmp esi, 16
	jae 2192f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2193f
2192:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+4]
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+8]
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+12]
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2193:
	cmp esi, 0
	jne 2191b
	mov eax, DWORD PTR [ebp]
	add eax, ebx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	add ebx, 4
	mov eax, DWORD PTR [ebx]
	add eax, DWORD PTR [edi+48]
	mov DWORD PTR [ebx], eax
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2194:
	cmp edx, 32
	jae 2195f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2196f
2195:
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
2196:
	cmp edx, 0
	jne 2194b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	add ebx, 4
	mov ebp, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	add ebp, edx
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	adc eax, 0
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2197f
	jmp 2198f
2197:
2199:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2199b
2198:
	and edi, 15
	jne 2200f
	jmp 2201f
2200:
2202:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2202b
2201:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2203:
	cmp edx, 32
	jae 2204f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2205f
2204:
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
2205:
	cmp edx, 0
	jne 2203b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	add ebx, 4
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+88]
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2206f
	jmp 2207f
2206:
2208:
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
	jne 2208b
2207:
	and edx, 15
	jne 2209f
	jmp 2210f
2209:
2211:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2211b
2210:
	mov edi, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [edi+36]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 0
	mov edi, DWORD PTR [edi+72]
	mov ebx, 0
2212:
	cmp esi, 16
	jae 2213f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2214f
2213:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2214:
	cmp esi, 0
	jne 2212b
	mov DWORD PTR [ebp], ebx
	mov eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ecx, DWORD PTR [edi+40]
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 0
	mov edi, DWORD PTR [edi+76]
	mov ebx, 0
2215:
	cmp esi, 16
	jae 2216f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2217f
2216:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+4]
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+8]
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+12]
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2217:
	cmp esi, 0
	jne 2215b
	mov eax, DWORD PTR [ebp]
	add eax, ebx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2218:
	cmp edx, 32
	jae 2219f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2220f
2219:
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
2220:
	cmp edx, 0
	jne 2218b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+36]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2221f
	jmp 2222f
2221:
2223:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2223b
2222:
	and edi, 15
	jne 2224f
	jmp 2225f
2224:
2226:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2226b
2225:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2227:
	cmp edx, 32
	jae 2228f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2229f
2228:
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
2229:
	cmp edx, 0
	jne 2227b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+40]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2230f
	jmp 2231f
2230:
2232:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2232b
2231:
	and edi, 15
	jne 2233f
	jmp 2234f
2233:
2235:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2235b
2234:
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov esi, ecx
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	add ebx, 4
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov ebx, DWORD PTR [edi+80]
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [edi+44]
	mul ecx
	mov ecx, eax
	mov DWORD PTR [edi+48], esi
	mov ebp, DWORD PTR [edi+80]
	mov esi, DWORD PTR [edi+96]
	add esi, 0
	mov edi, DWORD PTR [edi+60]
	mov ebx, 0
2236:
	cmp esi, 16
	jae 2237f
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	add edi, 4
	add ebp, 4
	sub esi, 4
	jmp 2238f
2237:
	mov eax, DWORD PTR [edi]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+4]
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+8]
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+12]
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ebx, edx
	add edi, 16
	add ebp, 16
	sub esi, 16
2238:
	cmp esi, 0
	jne 2236b
	mov eax, DWORD PTR [ebp]
	add eax, ebx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	add ebx, 4
	mov eax, DWORD PTR [ebx]
	add eax, DWORD PTR [edi+48]
	mov DWORD PTR [ebx], eax
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2239:
	cmp edx, 32
	jae 2240f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2241f
2240:
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
2241:
	cmp edx, 0
	jne 2239b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	add ebx, 4
	mov ebp, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	add ebp, edx
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	adc eax, 0
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+80]
	add ebx, 4
	mov edi, DWORD PTR [edi+96]
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2242f
	jmp 2243f
2242:
2244:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2244b
2243:
	and edi, 15
	jne 2245f
	jmp 2246f
2245:
2247:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2247b
2246:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2248:
	cmp edx, 32
	jae 2249f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2250f
2249:
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
2250:
	cmp edx, 0
	jne 2248b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	add ebx, 4
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, DWORD PTR [edi+80]
	add ebp, 4
	mov ebx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+92]
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2251f
	jmp 2252f
2251:
2253:
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
	jne 2253b
2252:
	and edx, 15
	jne 2254f
	jmp 2255f
2254:
2256:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2256b
2255:
	mov edi, DWORD PTR [esp+60]
	mov ecx, -1
	mov ebp, DWORD PTR [edi+52]
	mov ebx, DWORD PTR [edi+64]
	mov edi, DWORD PTR [edi+96]
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2257f
	jmp 2258f
2257:
2259:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2259b
2258:
	and edi, 15
	jne 2260f
	jmp 2261f
2260:
2262:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2262b
2261:
	mov edi, DWORD PTR [esp+60]
	mov ecx, -1
	mov ebp, DWORD PTR [edi+56]
	mov ebx, DWORD PTR [edi+68]
	mov edi, DWORD PTR [edi+96]
	add edi, 4
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2263f
	jmp 2264f
2263:
2265:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2265b
2264:
	and edi, 15
	jne 2266f
	jmp 2267f
2266:
2268:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2268b
2267:
	mov edi, DWORD PTR [esp+60]
	mov ecx, -1
	mov ebp, DWORD PTR [edi+88]
	mov ebx, DWORD PTR [edi+72]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2269f
	jmp 2270f
2269:
2271:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2271b
2270:
	and edi, 15
	jne 2272f
	jmp 2273f
2272:
2274:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2274b
2273:
	mov edi, DWORD PTR [esp+60]
	mov ecx, -1
	mov ebp, DWORD PTR [edi+92]
	mov ebx, DWORD PTR [edi+76]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2275f
	jmp 2276f
2275:
2277:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2277b
2276:
	and edi, 15
	jne 2278f
	jmp 2279f
2278:
2280:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2280b
2279:
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+100]
	sub esi, 1
	mov DWORD PTR [edi+100], esi
	test esi, esi
	jne 2115b
	mov ecx, -1
	mov ebp, DWORD PTR [edi+60]
	mov ebx, DWORD PTR [edi+84]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
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
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
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
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+72]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
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
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+72]
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
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
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+72]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2299f
	jmp 2300f
2299:
2301:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2301b
2300:
	and edi, 15
	jne 2302f
	jmp 2303f
2302:
2304:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2304b
2303:
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+96]
	add esi, 4
	shr esi, 1
	mov eax, esi
	add esi, eax
	add esi, eax
2305:
	mov ebp, DWORD PTR [edi+72]
	mov ebx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+72]
	mov ecx, 0
2306:
	cmp edx, 32
	jae 2307f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2308f
2307:
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
2308:
	cmp edx, 0
	jne 2306b
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+72]
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
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
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+72]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2312f
	jmp 2313f
2312:
2314:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2314b
2313:
	and edi, 15
	jne 2315f
	jmp 2316f
2315:
2317:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2317b
2316:
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, 0
	mov DWORD PTR [ebx], eax
	sub esi, 1
	test esi, esi
	jne 2305b
	mov ebp, DWORD PTR [edi+56]
	mov ecx, DWORD PTR [edi+96]
	add ecx, ecx
	mov eax, 0
2318:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2318b
	mov ebp, DWORD PTR [edi+56]
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+56]
	mov ecx, 0
2319:
	cmp edx, 32
	jae 2320f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2321f
2320:
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
2321:
	cmp edx, 0
	jne 2319b
	mov edi, DWORD PTR [esp+60]
	mov ebx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	add ebx, edx
	mov eax, DWORD PTR [ebx]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	xor ecx, -1
	mov ebp, DWORD PTR [edi+64]
	mov ebx, DWORD PTR [edi+56]
	mov edi, DWORD PTR [edi+96]
	add edi, 0
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
2328:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2328b
	mov ecx, -1
	mov ebp, DWORD PTR [edi+72]
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
	jne 2329f
	jmp 2330f
2329:
2331:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2331b
2330:
	and edi, 15
	jne 2332f
	jmp 2333f
2332:
2334:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2334b
2333:
	mov edi, DWORD PTR [esp+60]
273:
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
2335:
	cmp edx, 32
	jae 2336f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2337f
2336:
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
2337:
	cmp edx, 0
	jne 2335b
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
2338:
	cmp edx, 32
	jae 2339f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2340f
2339:
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
2340:
	cmp edx, 0
	jne 2338b
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
	and eax, DWORD PTR [edi+124]
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
	jne 2341f
	jmp 2342f
2341:
2343:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2343b
2342:
	and edi, 15
	jne 2344f
	jmp 2345f
2344:
2346:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2346b
2345:
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
	jne 2347f
	jmp 2348f
2347:
2349:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2349b
2348:
	and edi, 15
	jne 2350f
	jmp 2351f
2350:
2352:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2352b
2351:
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
2353:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2353b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2354:
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
2355:
	cmp edx, 32
	jae 2356f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2357f
2356:
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
2357:
	cmp edx, 0
	jne 2355b
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
2358:
	cmp edx, 32
	jae 2359f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2360f
2359:
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
2360:
	cmp edx, 0
	jne 2358b
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
2361:
	cmp edx, 32
	jae 2362f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2363f
2362:
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
2363:
	cmp edx, 0
	jne 2361b
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
	jne 2364f
	jmp 2365f
2364:
2366:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2366b
2365:
	and edi, 15
	jne 2367f
	jmp 2368f
2367:
2369:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2369b
2368:
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
	jne 2354b
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
	jne 2370f
	jmp 2371f
2370:
2372:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2372b
2371:
	and edi, 15
	jne 2373f
	jmp 2374f
2373:
2375:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2375b
2374:
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
	jne 2376f
	jmp 2377f
2376:
2378:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2378b
2377:
	and edi, 15
	jne 2379f
	jmp 2380f
2379:
2381:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2381b
2380:
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
2382:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2382b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2383:
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
2384:
	cmp edx, 32
	jae 2385f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2386f
2385:
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
2386:
	cmp edx, 0
	jne 2384b
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
2390:
	cmp edx, 32
	jae 2391f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2392f
2391:
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
2392:
	cmp edx, 0
	jne 2390b
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
	jne 2393f
	jmp 2394f
2393:
2395:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2395b
2394:
	and edi, 15
	jne 2396f
	jmp 2397f
2396:
2398:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2398b
2397:
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
	jne 2383b
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
	jne 2399f
	jmp 2400f
2399:
2401:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2401b
2400:
	and edi, 15
	jne 2402f
	jmp 2403f
2402:
2404:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2404b
2403:
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
2405:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2405b
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
	jne 2406f
	jmp 2407f
2406:
2408:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2408b
2407:
	and edi, 15
	jne 2409f
	jmp 2410f
2409:
2411:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2411b
2410:
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
2412:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2412b
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
	jne 2413f
	jmp 2414f
2413:
2415:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2415b
2414:
	and edi, 15
	jne 2416f
	jmp 2417f
2416:
2418:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2418b
2417:
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
2419:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2419b
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
	mov ebp, edi
	add ebp, 256
	add ebp, ecx
	add ebp, ecx
	add ebp, ecx
	add ebp, ecx
	mov eax, 0
25:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 25b
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
	mov ecx, DWORD PTR [esp+8]
	add ebp, ecx
	sub ebp, 1
	mov eax, 1
	mov BYTE PTR [ebp], al
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	mov eax, esi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add esi, eax
	add esi, 8
	mov eax, DWORD PTR [esp+8]
	add eax, eax
	add eax, eax
	add eax, eax
	sub esi, eax
26:
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
27:
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	adc eax, eax
	mov DWORD PTR [ebp], eax
	sbb ecx, ecx
	add ebx, 4
	add ebp, 4
	sub edx, 4
	jne 27b
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
28:
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 28b
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
29:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 29b
	mov edi, DWORD PTR [esp+20]
	sub esi, 1
	jne 26b
	mov esi, 6
210:
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
	jne 210b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, edi
	add esi, 256
	mov ebp, DWORD PTR [esp+4]
211:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 211b
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
212:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 212b
	mov eax, 1
21:
	mov ebx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi+4]
	mov esi, DWORD PTR [edi+8]
	mov edi, DWORD PTR [edi+12]
	ret
	.p2align 6
