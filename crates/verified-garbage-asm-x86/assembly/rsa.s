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
220:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 220b
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
221:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 221b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
222:
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
223:
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
	jne 223b
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
224:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 224b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
225:
	or ecx, DWORD PTR [ebp]
	add ebp, 4
	sub edx, 4
	jne 225b
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
	je 238f
	mov esi, 3
240:
	cmp esi, 3
	je 241f
	cmp esi, 2
	je 243f
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
	mov eax, DWORD PTR [esp+40]
	ror eax, 13
	add esi, eax
	jmp 244f
243:
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
	add esi, 2162688
244:
	jmp 242f
241:
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
	add esi, 2162688
242:
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
299:
	cmp edx, 32
	jae 2100f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2101f
2100:
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
2101:
	cmp edx, 0
	jne 299b
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
2108:
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
	jne 2109f
	jmp 2110f
2109:
2111:
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
	jne 2111b
2110:
	and edx, 15
	jne 2112f
	jmp 2113f
2112:
2114:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2114b
2113:
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
2115:
	cmp edx, 32
	jae 2116f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2117f
2116:
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
2117:
	cmp edx, 0
	jne 2115b
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
2118:
	cmp edx, 32
	jae 2119f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2120:
	cmp edx, 0
	jne 2118b
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
	jne 2124f
	jmp 2125f
2124:
2126:
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
	jne 2126b
2125:
	and edx, 15
	jne 2127f
	jmp 2128f
2127:
2129:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2129b
2128:
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
2130:
	cmp edx, 32
	jae 2131f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2132f
2131:
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
2132:
	cmp edx, 0
	jne 2130b
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
2133:
	cmp edx, 32
	jae 2134f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2135f
2134:
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
2135:
	cmp edx, 0
	jne 2133b
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
	jne 2139f
	jmp 2140f
2139:
2141:
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
	jne 2141b
2140:
	and edx, 15
	jne 2142f
	jmp 2143f
2142:
2144:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2144b
2143:
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
2145:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2145b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	sub esi, 65536
	cmp esi, 65536
	jae 2108b
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
2149:
	cmp edx, 32
	jae 2150f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2151f
2150:
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
2151:
	cmp edx, 0
	jne 2149b
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
	jne 240b
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
	jne 2155f
	jmp 2156f
2155:
2157:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2157b
2156:
	and edi, 15
	jne 2158f
	jmp 2159f
2158:
2160:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2160b
2159:
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
2167:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2167b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2168:
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
2169:
	cmp edx, 32
	jae 2170f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
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
2171:
	cmp edx, 0
	jne 2169b
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
2172:
	cmp edx, 32
	jae 2173f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2174f
2173:
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
2174:
	cmp edx, 0
	jne 2172b
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
2175:
	cmp edx, 32
	jae 2176f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2177:
	cmp edx, 0
	jne 2175b
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
	jne 2168b
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
2184:
	cmp edx, 32
	jae 2185f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2186:
	cmp edx, 0
	jne 2184b
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
2187:
	cmp edx, 32
	jae 2188f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2189:
	cmp edx, 0
	jne 2187b
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
	jne 2190f
	jmp 2191f
2190:
2192:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2192b
2191:
	and edi, 15
	jne 2193f
	jmp 2194f
2193:
2195:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2195b
2194:
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
2202:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2202b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2203:
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
2204:
	cmp edx, 32
	jae 2205f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2206f
2205:
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
2206:
	cmp edx, 0
	jne 2204b
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
2207:
	cmp edx, 32
	jae 2208f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2209f
2208:
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
2209:
	cmp edx, 0
	jne 2207b
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
2210:
	cmp edx, 32
	jae 2211f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2212:
	cmp edx, 0
	jne 2210b
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
	jne 2213f
	jmp 2214f
2213:
2215:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2215b
2214:
	and edi, 15
	jne 2216f
	jmp 2217f
2216:
2218:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2218b
2217:
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
	jne 2203b
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
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
	jmp 239f
238:
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
2228:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2228b
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
2229:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2229b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
2230:
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
2231:
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
	jne 2231b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	cmp eax, 2
	jne 2230b
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
2232:
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
	jne 2232b
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
2233:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2233b
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
	je 2234f
2236:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2236b
	jmp 2235f
2234:
2235:
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
2237:
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
2238:
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
	jne 2238b
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
2239:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2239b
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
2240:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2240b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2237b
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
2241:
	cmp edx, 32
	jae 2242f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2243f
2242:
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
2243:
	cmp edx, 0
	jne 2241b
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
2244:
	cmp edx, 32
	jae 2245f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2246f
2245:
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
2246:
	cmp edx, 0
	jne 2244b
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
2250:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2250b
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
2251:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2251b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
2252:
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
2253:
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
	jne 2253b
	mov DWORD PTR [ebp], ebx
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+96]
	add eax, 1
	mov DWORD PTR [edi+96], eax
	cmp eax, 2
	jne 2252b
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
2254:
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
	jne 2254b
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
2255:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2255b
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
	je 2256f
2258:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2258b
	jmp 2257f
2256:
2257:
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
2259:
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
2260:
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
	jne 2260b
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
2261:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2261b
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
2262:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2262b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2259b
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
2263:
	cmp edx, 32
	jae 2264f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2265:
	cmp edx, 0
	jne 2263b
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
2266:
	cmp edx, 32
	jae 2267f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2268f
2267:
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
2268:
	cmp edx, 0
	jne 2266b
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
2272:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2272b
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
2273:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2273b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
2274:
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
	mov ebx, 0
2275:
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
	jne 2275b
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
	jne 2274b
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
2276:
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
	jne 2276b
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
2277:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2277b
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
	je 2278f
2280:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2280b
	jmp 2279f
2278:
2279:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
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
2281:
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
2282:
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
	jne 2282b
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
2283:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2283b
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
2284:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2284b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2281b
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
2285:
	cmp edx, 32
	jae 2286f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2287f
2286:
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
2287:
	cmp edx, 0
	jne 2285b
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
2288:
	cmp edx, 32
	jae 2289f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2290f
2289:
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
2290:
	cmp edx, 0
	jne 2288b
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
2294:
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
	jne 2294b
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
2295:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2295b
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
	je 2296f
2298:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2298b
	jmp 2297f
2296:
2297:
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
2299:
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
2300:
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
	jne 2300b
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
2301:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2301b
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
2302:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2302b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2299b
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
2303:
	cmp edx, 32
	jae 2304f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2305f
2304:
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
2305:
	cmp edx, 0
	jne 2303b
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
2306:
	cmp edx, 32
	jae 2307f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2308:
	cmp edx, 0
	jne 2306b
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
2309:
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
	jne 2309b
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
2310:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2310b
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
	je 2311f
2313:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2313b
	jmp 2312f
2311:
2312:
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
2314:
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
2315:
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
	jne 2315b
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
2316:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2316b
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
2317:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2317b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2314b
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
2318:
	cmp edx, 32
	jae 2319f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2320:
	cmp edx, 0
	jne 2318b
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
2321:
	cmp edx, 32
	jae 2322f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2323:
	cmp edx, 0
	jne 2321b
	mov edi, DWORD PTR [esp+68]
	mov ebx, ecx
	and ebx, 1
	or ebx, DWORD PTR [edi+112]
	xor ebx, 1
	mov DWORD PTR [edi+116], ebx
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+120], eax
239:
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
210:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 210b
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
211:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 211b
	mov eax, 0
	mov DWORD PTR [edi+96], eax
212:
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
213:
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
	jne 213b
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
214:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 214b
	mov edx, DWORD PTR [esp+32]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
215:
	or ecx, DWORD PTR [ebp]
	add ebp, 4
	sub edx, 4
	jne 215b
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
	jne 216f
	jmp 217f
216:
218:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 218b
217:
	and edi, 15
	jne 219f
	jmp 220f
219:
221:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 221b
220:
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
234:
	cmp edx, 32
	jae 235f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
236:
	cmp edx, 0
	jne 234b
	mov edi, DWORD PTR [esp+60]
	mov ebx, ecx
	and ebx, 1
	mov eax, DWORD PTR [esp+32]
	and eax, 15
	je 237f
	cmp eax, eax
	jmp 238f
237:
	mov eax, DWORD PTR [esp+32]
	cmp eax, 128
	jae 239f
	cmp eax, eax
	jmp 240f
239:
	mov eax, DWORD PTR [esp+32]
	shr eax, 1
	add eax, 1
	mov ecx, DWORD PTR [esp+40]
	cmp ecx, eax
	jb 241f
	cmp eax, eax
	jmp 242f
241:
	mov ecx, DWORD PTR [esp+48]
	cmp ecx, eax
242:
240:
238:
	jb 243f
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
245:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	or ecx, eax
	add ebp, 4
	add ebx, 4
	sub edx, 4
	jne 245b
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
	jne 246f
	jmp 247f
246:
248:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 248b
247:
	and edi, 15
	jne 249f
	jmp 250f
249:
251:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 251b
250:
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
	jmp 244f
243:
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
	jne 255f
	jmp 256f
255:
257:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 257b
256:
	and edi, 15
	jne 258f
	jmp 259f
258:
260:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 260b
259:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+60]
	mov eax, DWORD PTR [ebp]
	xor eax, 1
	mov ebx, ebp
	add ebx, 4
	mov esi, DWORD PTR [edi+96]
	sub esi, 4
261:
	or eax, DWORD PTR [ebx]
	add ebx, 4
	sub esi, 4
	jne 261b
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
268:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 268b
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
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+76]
	mov ebx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+76]
	mov ecx, 0
275:
	cmp edx, 32
	jae 276f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 277f
276:
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
277:
	cmp edx, 0
	jne 275b
	mov edi, DWORD PTR [esp+60]
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov ebp, DWORD PTR [edi+60]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
278:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi], eax
	add ebp, 4
	add esi, 16
	sub ecx, 1
	jne 278b
	mov esi, DWORD PTR [edi+64]
	add esi, 16
	mov ebp, DWORD PTR [edi+76]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
279:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi+4], eax
	add ebp, 4
	add esi, 16
	sub ecx, 1
	jne 279b
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
280:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 280b
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
281:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi], eax
	add ebp, 4
	add esi, 20
	sub ecx, 1
	jne 281b
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
282:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi+4], eax
	add ebp, 4
	add esi, 20
	sub ecx, 1
	jne 282b
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov ebp, DWORD PTR [edi+60]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
283:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [esi+16], eax
	add ebp, 4
	add esi, 20
	sub ecx, 1
	jne 283b
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
284:
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
285:
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
	jne 285b
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
286:
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
	jne 286b
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
287:
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
	jne 287b
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
288:
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
	jne 288b
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
289:
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
	jne 289b
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
290:
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
	jne 290b
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
291:
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
	jne 291b
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
292:
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
	jne 292b
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
293:
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
	jne 293b
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
294:
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
	jne 294b
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
	jne 284b
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
295:
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
	jne 295b
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
296:
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
	jne 296b
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
297:
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
	jne 297b
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
298:
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
	jne 298b
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
299:
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
	jne 299b
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
2100:
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp], eax
	add ebp, 4
	add esi, 16
	sub ecx, 1
	jne 2100b
	mov esi, DWORD PTR [edi+80]
	add esi, 20
	mov ebp, DWORD PTR [edi+76]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	shr ecx, 2
2101:
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp], eax
	add ebp, 4
	add esi, 20
	sub ecx, 1
	jne 2101b
	mov ebp, DWORD PTR [edi+84]
	mov ecx, DWORD PTR [edi+96]
	add ecx, 4
	mov eax, 0
2102:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2102b
	mov ebp, DWORD PTR [edi+84]
	mov ebx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2103:
	cmp edx, 32
	jae 2104f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2105f
2104:
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
2105:
	cmp edx, 0
	jne 2103b
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
	jne 2106f
	jmp 2107f
2106:
2108:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2108b
2107:
	and edi, 15
	jne 2109f
	jmp 2110f
2109:
2111:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2111b
2110:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+76]
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2112:
	cmp edx, 32
	jae 2113f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2114f
2113:
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
2114:
	cmp edx, 0
	jne 2112b
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
	jne 2115f
	jmp 2116f
2115:
2117:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2117b
2116:
	and edi, 15
	jne 2118f
	jmp 2119f
2118:
2120:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2120b
2119:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+76]
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 4
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2121:
	cmp edx, 32
	jae 2122f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
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
2123:
	cmp edx, 0
	jne 2121b
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
	jne 2124f
	jmp 2125f
2124:
2126:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2126b
2125:
	and edi, 15
	jne 2127f
	jmp 2128f
2127:
2129:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2129b
2128:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+76]
	mov ebx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+84]
	mov ecx, 0
2130:
	cmp edx, 32
	jae 2131f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2132f
2131:
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
2132:
	cmp edx, 0
	jne 2130b
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
	jne 2133f
	jmp 2134f
2133:
2135:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2135b
2134:
	and edi, 15
	jne 2136f
	jmp 2137f
2136:
2138:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2138b
2137:
	mov edi, DWORD PTR [esp+60]
	mov ebp, DWORD PTR [edi+56]
	mov ecx, DWORD PTR [edi+96]
	add ecx, ecx
	mov eax, 0
2139:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2139b
	mov ebp, DWORD PTR [edi+56]
	mov ebx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+96]
	add edx, 0
	mov edi, DWORD PTR [edi+56]
	mov ecx, 0
2140:
	cmp edx, 32
	jae 2141f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2142f
2141:
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
2142:
	cmp edx, 0
	jne 2140b
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
	jne 2143f
	jmp 2144f
2143:
2145:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2145b
2144:
	and edi, 15
	jne 2146f
	jmp 2147f
2146:
2148:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2148b
2147:
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
2149:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2149b
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
	jne 2150f
	jmp 2151f
2150:
2152:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2152b
2151:
	and edi, 15
	jne 2153f
	jmp 2154f
2153:
2155:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2155b
2154:
	mov edi, DWORD PTR [esp+60]
244:
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
2156:
	cmp edx, 32
	jae 2157f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2158f
2157:
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
2158:
	cmp edx, 0
	jne 2156b
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
2159:
	cmp edx, 32
	jae 2160f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2161f
2160:
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
2161:
	cmp edx, 0
	jne 2159b
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
	jne 2162f
	jmp 2163f
2162:
2164:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2164b
2163:
	and edi, 15
	jne 2165f
	jmp 2166f
2165:
2167:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2167b
2166:
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
	je 2174f
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
2176:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2176b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2177:
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
2181:
	cmp edx, 32
	jae 2182f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
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
2183:
	cmp edx, 0
	jne 2181b
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
2184:
	cmp edx, 32
	jae 2185f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2186:
	cmp edx, 0
	jne 2184b
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
	jne 2187f
	jmp 2188f
2187:
2189:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2189b
2188:
	and edi, 15
	jne 2190f
	jmp 2191f
2190:
2192:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2192b
2191:
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
	jne 2177b
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
2205:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2205b
	mov esi, DWORD PTR [esp+32]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2206:
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
2207:
	cmp edx, 32
	jae 2208f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2209f
2208:
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
2209:
	cmp edx, 0
	jne 2207b
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
2213:
	cmp edx, 32
	jae 2214f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2215:
	cmp edx, 0
	jne 2213b
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
	jne 2216f
	jmp 2217f
2216:
2218:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2218b
2217:
	and edi, 15
	jne 2219f
	jmp 2220f
2219:
2221:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2221b
2220:
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
	jne 2206b
	jmp 2175f
2174:
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
2222:
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
	jne 2222b
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
2223:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2223b
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
	je 2224f
2226:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2226b
	jmp 2225f
2224:
2225:
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
2227:
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
2228:
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
	jne 2228b
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
2229:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2229b
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
2230:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2230b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2227b
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
2243:
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
	jne 2243b
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
2244:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2244b
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
	je 2245f
2247:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2247b
	jmp 2246f
2245:
2246:
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
2248:
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
2249:
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
	jne 2249b
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
2250:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 2250b
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
2251:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 2251b
	mov edi, DWORD PTR [esp+60]
	mov eax, DWORD PTR [edi+72]
	sub eax, 1
	mov DWORD PTR [edi+72], eax
	jne 2248b
2175:
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
	jne 2252f
	jmp 2253f
2252:
2254:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2254b
2253:
	and edi, 15
	jne 2255f
	jmp 2256f
2255:
2257:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2257b
2256:
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
2258:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2258b
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
	jne 2259f
	jmp 2260f
2259:
2261:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2261b
2260:
	and edi, 15
	jne 2262f
	jmp 2263f
2262:
2264:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2264b
2263:
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
2265:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2265b
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
	jne 2266f
	jmp 2267f
2266:
2268:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2268b
2267:
	and edi, 15
	jne 2269f
	jmp 2270f
2269:
2271:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2271b
2270:
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
2272:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2272b
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
