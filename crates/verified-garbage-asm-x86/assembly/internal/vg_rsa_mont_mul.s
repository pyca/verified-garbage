// The functions of `src/internal/vg_rsa_mont_mul.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_mont_mul:
	push ebx
	push esi
	push edi
	push ebp
	mov ebp, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+32]
	add eax, eax
	add eax, eax
	add eax, eax
	add ebp, eax
	mov ebp, DWORD PTR [ebp+64]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+36]
	add eax, eax
	add eax, eax
	add eax, eax
	add edi, eax
	mov edi, DWORD PTR [edi+64]
	mov edx, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+28]
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	mov edx, DWORD PTR [edx+64]
	mov ebx, DWORD PTR [esp+20]
	mov esi, DWORD PTR [ebx+64]
	mov ecx, DWORD PTR [ebx+80]
	mov eax, DWORD PTR [ebx+48]
	add eax, eax
	add eax, eax
	add eax, eax
	add ebx, 56
	push eax
	push ebx
	push ecx
	push edx
	push esi
	push edi
	push ebp
	lea esp, [esp-12]
	stmxcsr DWORD PTR [esp+4]
	mov eax, 8127
	mov DWORD PTR [esp], eax
	ldmxcsr DWORD PTR [esp]
	lfence
	mov ebx, DWORD PTR [esp+28]
	add ebx, 24
	mov eax, DWORD PTR [esp+36]
	add ebx, eax
	add ebx, eax
	mov esi, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+36]
20:
	mov eax, DWORD PTR [esi]
	sub ebx, 4
	mov DWORD PTR [ebx], eax
	add esi, 4
	sub edi, 4
	jne 20b
	mov ebx, DWORD PTR [esp+28]
	mov eax, 0
	mov DWORD PTR [ebx+16], eax
	mov DWORD PTR [ebx+20], eax
	mov ecx, 0
	pxor xmm6, xmm6
	mov eax, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	cmp eax, ebx
	je 21f
23:
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	mov ebp, ecx
	add ebp, 4
	mov esi, DWORD PTR [esp+28]
	add esi, 24
	mov eax, DWORD PTR [esp+36]
	add esi, eax
	add esi, eax
	sub esi, ebp
	mov edi, DWORD PTR [esp+16]
	cmp ebp, 32
	jae 24f
	jmp 25f
24:
26:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [esi+16]
	movdqu xmm3, XMMWORD PTR [edi+16]
	pshufd xmm7, xmm5, 49
	pmuludq xmm5, xmm3
	psrlq xmm3, 32
	pmuludq xmm7, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
	add esi, 32
	add edi, 32
	sub ebp, 32
	cmp ebp, 32
	jae 26b
25:
	cmp ebp, 16
	jb 27f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 28f
27:
28:
	cmp ebp, 8
	jae 29f
	jmp 210f
29:
	movq xmm5, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm5, xmm5
	punpckldq xmm3, xmm3
	pmuludq xmm5, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	add esi, 8
	add edi, 8
	sub ebp, 8
210:
	cmp ebp, 4
	jae 211f
	jmp 212f
211:
	mov eax, DWORD PTR [esi]
	movd xmm7, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm7, xmm3
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
212:
	mov ebp, ecx
	sub ebp, 8
	jae 213f
	mov ebp, 0
	jmp 214f
213:
214:
	mov esi, DWORD PTR [esp+28]
	add esi, 32
	mov eax, DWORD PTR [esp+36]
	add esi, eax
	sub esi, ecx
	mov edi, DWORD PTR [esp+20]
	add edi, 12
	cmp ebp, 32
	jae 215f
	jmp 216f
215:
217:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [esi+16]
	movdqu xmm3, XMMWORD PTR [edi+16]
	pshufd xmm7, xmm5, 49
	pmuludq xmm5, xmm3
	psrlq xmm3, 32
	pmuludq xmm7, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
	add esi, 32
	add edi, 32
	sub ebp, 32
	cmp ebp, 32
	jae 217b
216:
	cmp ebp, 16
	jb 218f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 219f
218:
219:
	cmp ebp, 8
	jae 220f
	jmp 221f
220:
	movq xmm5, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm5, xmm5
	punpckldq xmm3, xmm3
	pmuludq xmm5, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	add esi, 8
	add edi, 8
	sub ebp, 8
221:
	cmp ebp, 4
	jae 222f
	jmp 223f
222:
	mov eax, DWORD PTR [esi]
	movd xmm7, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm7, xmm3
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
223:
	mov eax, DWORD PTR [esp+36]
	cmp eax, 12
	mov eax, DWORD PTR [esp+20]
	jae 224f
	mov eax, DWORD PTR [eax+4]
	movd xmm4, eax
	jmp 225f
224:
	movq xmm4, QWORD PTR [eax+4]
	punpckldq xmm4, xmm4
225:
	movdqa xmm2, xmm6
	pmuludq xmm2, xmm4
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	movdqa xmm2, xmm0
	psrldq xmm2, 8
	paddq xmm0, xmm2
	movdqa xmm2, xmm1
	psrldq xmm2, 8
	paddq xmm1, xmm2
	mov ebx, DWORD PTR [esp+28]
	movq QWORD PTR [ebx], xmm0
	movq QWORD PTR [ebx+8], xmm1
	mov eax, DWORD PTR [ebx]
	add eax, DWORD PTR [ebx+16]
	mov edx, DWORD PTR [ebx+4]
	adc edx, DWORD PTR [ebx+20]
	mov esi, edx
	mov edi, eax
	mov edx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [edx]
	mul edx
	mov edx, DWORD PTR [esp+36]
	add edx, ebx
	sub edx, ecx
	mov DWORD PTR [edx+20], eax
	movd xmm1, eax
	punpcklqdq xmm1, xmm6
	movdqa xmm6, xmm1
	mov edx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [edx]
	mul edx
	add eax, edi
	adc esi, edx
	mov eax, DWORD PTR [ebx+8]
	add eax, edx
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [ebx+12]
	adc eax, 0
	mov DWORD PTR [ebx+12], eax
	mov edx, esi
	mov DWORD PTR [ebx+16], edx
	cmp edx, DWORD PTR [ebx+8]
	mov eax, DWORD PTR [ebx+12]
	adc eax, 0
	mov DWORD PTR [ebx+20], eax
	add ecx, 4
	mov eax, DWORD PTR [esp+36]
	cmp ecx, eax
	jne 23b
226:
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	mov eax, DWORD PTR [esp+36]
	mov ebp, eax
	add ebp, eax
	sub ebp, 4
	sub ebp, ecx
	mov esi, DWORD PTR [esp+28]
	add esi, 24
	mov eax, DWORD PTR [esp+36]
	add esi, eax
	mov edi, DWORD PTR [esp+16]
	add edi, ecx
	add edi, 4
	sub edi, eax
	cmp ebp, 32
	jae 227f
	jmp 228f
227:
229:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [esi+16]
	movdqu xmm3, XMMWORD PTR [edi+16]
	pshufd xmm7, xmm5, 49
	pmuludq xmm5, xmm3
	psrlq xmm3, 32
	pmuludq xmm7, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
	add esi, 32
	add edi, 32
	sub ebp, 32
	cmp ebp, 32
	jae 229b
228:
	cmp ebp, 16
	jb 230f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 231f
230:
231:
	cmp ebp, 8
	jae 232f
	jmp 233f
232:
	movq xmm5, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm5, xmm5
	punpckldq xmm3, xmm3
	pmuludq xmm5, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	add esi, 8
	add edi, 8
	sub ebp, 8
233:
	cmp ebp, 4
	jae 234f
	jmp 235f
234:
	mov eax, DWORD PTR [esi]
	movd xmm7, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm7, xmm3
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
235:
	mov eax, DWORD PTR [esp+36]
	mov ebp, eax
	add ebp, eax
	sub ebp, 4
	sub ebp, ecx
	mov esi, DWORD PTR [esp+28]
	add esi, 24
	mov eax, DWORD PTR [esp+36]
	mov edi, DWORD PTR [esp+20]
	add edi, ecx
	add edi, 4
	sub edi, eax
	cmp ebp, 32
	jae 236f
	jmp 237f
236:
238:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [esi+16]
	movdqu xmm3, XMMWORD PTR [edi+16]
	pshufd xmm7, xmm5, 49
	pmuludq xmm5, xmm3
	psrlq xmm3, 32
	pmuludq xmm7, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
	add esi, 32
	add edi, 32
	sub ebp, 32
	cmp ebp, 32
	jae 238b
237:
	cmp ebp, 16
	jb 239f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 240f
239:
240:
	cmp ebp, 8
	jae 241f
	jmp 242f
241:
	movq xmm5, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm5, xmm5
	punpckldq xmm3, xmm3
	pmuludq xmm5, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	add esi, 8
	add edi, 8
	sub ebp, 8
242:
	cmp ebp, 4
	jae 243f
	jmp 244f
243:
	mov eax, DWORD PTR [esi]
	movd xmm7, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm7, xmm3
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
244:
	movdqa xmm2, xmm0
	psrldq xmm2, 8
	paddq xmm0, xmm2
	movdqa xmm2, xmm1
	psrldq xmm2, 8
	paddq xmm1, xmm2
	mov ebx, DWORD PTR [esp+28]
	movq QWORD PTR [ebx], xmm0
	movq QWORD PTR [ebx+8], xmm1
	mov eax, DWORD PTR [ebx]
	add eax, DWORD PTR [ebx+16]
	mov edx, DWORD PTR [ebx+4]
	adc edx, DWORD PTR [ebx+20]
	mov esi, DWORD PTR [esp+36]
	add esi, esi
	add esi, ebx
	sub esi, ecx
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [ebx+16], edx
	cmp edx, DWORD PTR [ebx+8]
	mov eax, DWORD PTR [ebx+12]
	adc eax, 0
	mov DWORD PTR [ebx+20], eax
	add ecx, 4
	mov eax, DWORD PTR [esp+36]
	add eax, eax
	cmp ecx, eax
	jne 226b
	jmp 22f
21:
245:
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	mov ebx, ecx
	add ebx, 4
	shr ebx, 3
	add ebx, ebx
	add ebx, ebx
	mov ebp, ebx
	mov esi, DWORD PTR [esp+28]
	add esi, 24
	mov eax, DWORD PTR [esp+36]
	add esi, eax
	add esi, eax
	sub esi, ebx
	mov edi, DWORD PTR [esp+12]
	add edi, ecx
	add edi, 4
	sub edi, ebx
	cmp ebp, 32
	jae 246f
	jmp 247f
246:
248:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [esi+16]
	movdqu xmm3, XMMWORD PTR [edi+16]
	pshufd xmm7, xmm5, 49
	pmuludq xmm5, xmm3
	psrlq xmm3, 32
	pmuludq xmm7, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
	add esi, 32
	add edi, 32
	sub ebp, 32
	cmp ebp, 32
	jae 248b
247:
	cmp ebp, 16
	jb 249f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 250f
249:
250:
	cmp ebp, 8
	jae 251f
	jmp 252f
251:
	movq xmm5, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm5, xmm5
	punpckldq xmm3, xmm3
	pmuludq xmm5, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	add esi, 8
	add edi, 8
	sub ebp, 8
252:
	cmp ebp, 4
	jae 253f
	jmp 254f
253:
	mov eax, DWORD PTR [esi]
	movd xmm7, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm7, xmm3
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
254:
	paddq xmm0, xmm0
	paddq xmm1, xmm1
	mov eax, ebx
	add eax, eax
	cmp eax, ecx
	je 255f
	jmp 256f
255:
	mov esi, DWORD PTR [esp+12]
	add esi, ebx
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	pmuludq xmm2, xmm2
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
256:
	mov ebp, ecx
	sub ebp, 8
	jae 257f
	mov ebp, 0
	jmp 258f
257:
258:
	mov esi, DWORD PTR [esp+28]
	add esi, 32
	mov eax, DWORD PTR [esp+36]
	add esi, eax
	sub esi, ecx
	mov edi, DWORD PTR [esp+20]
	add edi, 12
	cmp ebp, 32
	jae 259f
	jmp 260f
259:
261:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [esi+16]
	movdqu xmm3, XMMWORD PTR [edi+16]
	pshufd xmm7, xmm5, 49
	pmuludq xmm5, xmm3
	psrlq xmm3, 32
	pmuludq xmm7, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
	add esi, 32
	add edi, 32
	sub ebp, 32
	cmp ebp, 32
	jae 261b
260:
	cmp ebp, 16
	jb 262f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 263f
262:
263:
	cmp ebp, 8
	jae 264f
	jmp 265f
264:
	movq xmm5, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm5, xmm5
	punpckldq xmm3, xmm3
	pmuludq xmm5, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	add esi, 8
	add edi, 8
	sub ebp, 8
265:
	cmp ebp, 4
	jae 266f
	jmp 267f
266:
	mov eax, DWORD PTR [esi]
	movd xmm7, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm7, xmm3
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
267:
	mov eax, DWORD PTR [esp+36]
	cmp eax, 12
	mov eax, DWORD PTR [esp+20]
	jae 268f
	mov eax, DWORD PTR [eax+4]
	movd xmm4, eax
	jmp 269f
268:
	movq xmm4, QWORD PTR [eax+4]
	punpckldq xmm4, xmm4
269:
	movdqa xmm2, xmm6
	pmuludq xmm2, xmm4
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	movdqa xmm2, xmm0
	psrldq xmm2, 8
	paddq xmm0, xmm2
	movdqa xmm2, xmm1
	psrldq xmm2, 8
	paddq xmm1, xmm2
	mov ebx, DWORD PTR [esp+28]
	movq QWORD PTR [ebx], xmm0
	movq QWORD PTR [ebx+8], xmm1
	mov eax, DWORD PTR [ebx]
	add eax, DWORD PTR [ebx+16]
	mov edx, DWORD PTR [ebx+4]
	adc edx, DWORD PTR [ebx+20]
	mov esi, edx
	mov edi, eax
	mov edx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [edx]
	mul edx
	mov edx, DWORD PTR [esp+36]
	add edx, ebx
	sub edx, ecx
	mov DWORD PTR [edx+20], eax
	movd xmm1, eax
	punpcklqdq xmm1, xmm6
	movdqa xmm6, xmm1
	mov edx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [edx]
	mul edx
	add eax, edi
	adc esi, edx
	mov eax, DWORD PTR [ebx+8]
	add eax, edx
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [ebx+12]
	adc eax, 0
	mov DWORD PTR [ebx+12], eax
	mov edx, esi
	mov DWORD PTR [ebx+16], edx
	cmp edx, DWORD PTR [ebx+8]
	mov eax, DWORD PTR [ebx+12]
	adc eax, 0
	mov DWORD PTR [ebx+20], eax
	add ecx, 4
	mov eax, DWORD PTR [esp+36]
	cmp ecx, eax
	jne 245b
270:
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	mov ebx, ecx
	add ebx, 4
	shr ebx, 3
	add ebx, ebx
	add ebx, ebx
	mov eax, DWORD PTR [esp+36]
	mov ebp, ebx
	add ebp, eax
	sub ebp, ecx
	sub ebp, 4
	mov esi, DWORD PTR [esp+28]
	add esi, 24
	mov eax, DWORD PTR [esp+36]
	add esi, eax
	add esi, eax
	sub esi, ebx
	mov edi, DWORD PTR [esp+12]
	add edi, ecx
	add edi, 4
	sub edi, ebx
	cmp ebp, 32
	jae 271f
	jmp 272f
271:
273:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [esi+16]
	movdqu xmm3, XMMWORD PTR [edi+16]
	pshufd xmm7, xmm5, 49
	pmuludq xmm5, xmm3
	psrlq xmm3, 32
	pmuludq xmm7, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
	add esi, 32
	add edi, 32
	sub ebp, 32
	cmp ebp, 32
	jae 273b
272:
	cmp ebp, 16
	jb 274f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 275f
274:
275:
	cmp ebp, 8
	jae 276f
	jmp 277f
276:
	movq xmm5, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm5, xmm5
	punpckldq xmm3, xmm3
	pmuludq xmm5, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	add esi, 8
	add edi, 8
	sub ebp, 8
277:
	cmp ebp, 4
	jae 278f
	jmp 279f
278:
	mov eax, DWORD PTR [esi]
	movd xmm7, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm7, xmm3
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
279:
	paddq xmm0, xmm0
	paddq xmm1, xmm1
	mov eax, ebx
	add eax, eax
	cmp eax, ecx
	je 280f
	jmp 281f
280:
	mov esi, DWORD PTR [esp+12]
	add esi, ebx
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	pmuludq xmm2, xmm2
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
281:
	mov eax, DWORD PTR [esp+36]
	mov ebp, eax
	add ebp, eax
	sub ebp, 4
	sub ebp, ecx
	mov esi, DWORD PTR [esp+28]
	add esi, 24
	mov eax, DWORD PTR [esp+36]
	mov edi, DWORD PTR [esp+20]
	add edi, ecx
	add edi, 4
	sub edi, eax
	cmp ebp, 32
	jae 282f
	jmp 283f
282:
284:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [esi+16]
	movdqu xmm3, XMMWORD PTR [edi+16]
	pshufd xmm7, xmm5, 49
	pmuludq xmm5, xmm3
	psrlq xmm3, 32
	pmuludq xmm7, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
	add esi, 32
	add edi, 32
	sub ebp, 32
	cmp ebp, 32
	jae 284b
283:
	cmp ebp, 16
	jb 285f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pmuludq xmm2, xmm3
	psrlq xmm3, 32
	pmuludq xmm4, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 286f
285:
286:
	cmp ebp, 8
	jae 287f
	jmp 288f
287:
	movq xmm5, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm5, xmm5
	punpckldq xmm3, xmm3
	pmuludq xmm5, xmm3
	paddq xmm0, xmm5
	psrlq xmm5, 32
	paddq xmm1, xmm5
	add esi, 8
	add edi, 8
	sub ebp, 8
288:
	cmp ebp, 4
	jae 289f
	jmp 290f
289:
	mov eax, DWORD PTR [esi]
	movd xmm7, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm7, xmm3
	paddq xmm0, xmm7
	psrlq xmm7, 32
	paddq xmm1, xmm7
290:
	movdqa xmm2, xmm0
	psrldq xmm2, 8
	paddq xmm0, xmm2
	movdqa xmm2, xmm1
	psrldq xmm2, 8
	paddq xmm1, xmm2
	mov ebx, DWORD PTR [esp+28]
	movq QWORD PTR [ebx], xmm0
	movq QWORD PTR [ebx+8], xmm1
	mov eax, DWORD PTR [ebx]
	add eax, DWORD PTR [ebx+16]
	mov edx, DWORD PTR [ebx+4]
	adc edx, DWORD PTR [ebx+20]
	mov esi, DWORD PTR [esp+36]
	add esi, esi
	add esi, ebx
	sub esi, ecx
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [ebx+16], edx
	cmp edx, DWORD PTR [ebx+8]
	mov eax, DWORD PTR [ebx+12]
	adc eax, 0
	mov DWORD PTR [ebx+20], eax
	add ecx, 4
	mov eax, DWORD PTR [esp+36]
	add eax, eax
	cmp ecx, eax
	jne 270b
22:
	lfence
	ldmxcsr DWORD PTR [esp+4]
	lea esp, [esp+12]
	mov ebp, DWORD PTR [esp+16]
	add ebp, 24
	mov eax, DWORD PTR [esp+24]
	add ebp, eax
	mov ebx, ebp
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+24]
	mov ecx, 0
291:
	sub ebp, 4
	mov eax, DWORD PTR [ebp]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [esi]
	mov DWORD PTR [ebx], eax
	sbb ecx, ecx
	add esi, 4
	add ebx, 4
	sub edi, 4
	jne 291b
	mov eax, DWORD PTR [esp+16]
	mov eax, DWORD PTR [eax+16]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, DWORD PTR [esp+16]
	add ebp, 24
	mov eax, DWORD PTR [esp+24]
	add ebp, eax
	mov ebx, ebp
	mov esi, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+24]
292:
	sub ebp, 4
	mov eax, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebx]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [esi], eax
	add ebx, 4
	add esi, 4
	sub edi, 4
	jne 292b
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [esp]
	mov edi, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
