// The functions of `src/internal/vg_rsa_keygen_inverse.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_inverse:
	push ebx
	push ebp
	push esi
	push edi
	mov edi, DWORD PTR [esp+20]
	mov esi, DWORD PTR [esp+28]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
20:
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+100], eax
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
21:
	cmp edx, 32
	jae 22f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 23f
22:
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
23:
	cmp edx, 0
	jne 21b
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+104], ebx
	mov eax, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+108], eax
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
24:
	cmp edx, 32
	jae 25f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 26f
25:
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
26:
	cmp edx, 0
	jne 24b
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 27f
	jmp 28f
27:
29:
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
	jne 29b
28:
	and edx, 15
	jne 210f
	jmp 211f
210:
212:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 212b
211:
	mov edi, DWORD PTR [esp+20]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 213f
	jmp 214f
213:
215:
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
	jne 215b
214:
	and edx, 15
	jne 216f
	jmp 217f
216:
218:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 218b
217:
	mov edi, DWORD PTR [esp+20]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 219f
	jmp 220f
219:
221:
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
	jne 221b
220:
	and edx, 15
	jne 222f
	jmp 223f
222:
224:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 224b
223:
	mov edi, DWORD PTR [esp+20]
	mov ebx, 0
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
225:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 225b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
226:
	cmp edx, 32
	jae 227f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 228f
227:
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
228:
	cmp edx, 0
	jne 226b
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+104], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 229f
	jmp 230f
229:
231:
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
	jne 231b
230:
	and edx, 15
	jne 232f
	jmp 233f
232:
234:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 234b
233:
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
235:
	cmp edx, 32
	jae 236f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 237f
236:
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
237:
	cmp edx, 0
	jne 235b
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
238:
	cmp edx, 32
	jae 239f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 240f
239:
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
240:
	cmp edx, 0
	jne 238b
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+104], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 241f
	jmp 242f
241:
243:
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
	jne 243b
242:
	and edx, 15
	jne 244f
	jmp 245f
244:
246:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 246b
245:
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
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
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 250f
	jmp 251f
250:
252:
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
	jne 252b
251:
	and edx, 15
	jne 253f
	jmp 254f
253:
255:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 255b
254:
	mov edi, DWORD PTR [esp+20]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 256f
	jmp 257f
256:
258:
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
	jne 258b
257:
	and edx, 15
	jne 259f
	jmp 260f
259:
261:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 261b
260:
	mov edi, DWORD PTR [esp+20]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 262f
	jmp 263f
262:
264:
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
	jne 264b
263:
	and edx, 15
	jne 265f
	jmp 266f
265:
267:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 267b
266:
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+104], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 268f
	jmp 269f
268:
270:
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
	jne 270b
269:
	and edx, 15
	jne 271f
	jmp 272f
271:
273:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 273b
272:
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
274:
	cmp edx, 32
	jae 275f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 276f
275:
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
276:
	cmp edx, 0
	jne 274b
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	xor ebx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
277:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 277b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+100], eax
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
278:
	cmp edx, 32
	jae 279f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 280f
279:
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
280:
	cmp edx, 0
	jne 278b
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+104], ebx
	mov eax, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+108], eax
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
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
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 284f
	jmp 285f
284:
286:
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
	jne 286b
285:
	and edx, 15
	jne 287f
	jmp 288f
287:
289:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 289b
288:
	mov edi, DWORD PTR [esp+20]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 290f
	jmp 291f
290:
292:
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
	jne 292b
291:
	and edx, 15
	jne 293f
	jmp 294f
293:
295:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 295b
294:
	mov edi, DWORD PTR [esp+20]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 296f
	jmp 297f
296:
298:
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
	jne 298b
297:
	and edx, 15
	jne 299f
	jmp 2100f
299:
2101:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2101b
2100:
	mov edi, DWORD PTR [esp+20]
	mov ebx, 0
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
2102:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2102b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
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
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+104], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2106f
	jmp 2107f
2106:
2108:
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
	jne 2108b
2107:
	and edx, 15
	jne 2109f
	jmp 2110f
2109:
2111:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2111b
2110:
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2112:
	cmp edx, 32
	jae 2113f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
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
2114:
	cmp edx, 0
	jne 2112b
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
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
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov DWORD PTR [edi+104], ebx
	mov ecx, 0
	sub ecx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2118f
	jmp 2119f
2118:
2120:
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
	jne 2120b
2119:
	and edx, 15
	jne 2121f
	jmp 2122f
2121:
2123:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2123b
2122:
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
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
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2127f
	jmp 2128f
2127:
2129:
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
	jne 2129b
2128:
	and edx, 15
	jne 2130f
	jmp 2131f
2130:
2132:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2132b
2131:
	mov edi, DWORD PTR [esp+20]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edx
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	jne 2133f
	jmp 2134f
2133:
2135:
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
	jne 2135b
2134:
	and edx, 15
	jne 2136f
	jmp 2137f
2136:
2138:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 2138b
2137:
	mov edi, DWORD PTR [esp+20]
	mov ecx, 0
	sub ecx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
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
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov eax, edi
	add eax, 160
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov DWORD PTR [edi+104], eax
	mov ecx, 0
	sub ecx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
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
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebx, edi
	add ebx, 160
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov edi, edi
	add edi, 160
	add edi, edx
	add edi, edx
	mov edx, DWORD PTR [esp+28]
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
	mov edi, DWORD PTR [esp+20]
	mov ebx, ecx
	and ebx, 1
	xor ebx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebp, edx
	mov DWORD PTR [ebp], ebx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 8
	mov ebp, edi
	add ebp, 160
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+28]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
2154:
	mov eax, DWORD PTR [ebp+4]
	and eax, 1
	ror eax, 1
	mov ecx, DWORD PTR [ebp]
	shr ecx, 1
	add ecx, eax
	mov DWORD PTR [ebp], ecx
	add ebp, 4
	sub edx, 4
	jne 2154b
	mov eax, DWORD PTR [ebp]
	shr eax, 1
	mov DWORD PTR [ebp], eax
	sub esi, 1
	cmp esi, 0
	jne 20b
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
