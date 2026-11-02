// The functions of `src/internal/vg_rsa_mont_mul_at.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_mont_mul_at:
	push ebx
	push esi
	push edi
	push ebp
	mov ebp, DWORD PTR [esp+20]
	add ebp, DWORD PTR [esp+48]
	mov edi, DWORD PTR [esp+20]
	add edi, DWORD PTR [esp+52]
	mov esi, DWORD PTR [esp+20]
	add esi, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+20]
	add edx, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [esp+20]
	add ecx, DWORD PTR [esp+40]
	mov ebx, DWORD PTR [esp+20]
	add ebx, DWORD PTR [esp+36]
	mov eax, DWORD PTR [esp+28]
	add eax, eax
	add eax, eax
	add eax, eax
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
	mov eax, DWORD PTR [esp+20]
	mov ebx, DWORD PTR [eax+4]
	movd xmm7, ebx
	mov ebx, DWORD PTR [esp+36]
	cmp ebx, 12
	jb 21f
	mov ebx, DWORD PTR [eax+8]
	movd xmm2, ebx
	punpcklqdq xmm7, xmm2
	jmp 22f
21:
22:
	mov eax, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	cmp eax, ebx
	je 23f
25:
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
	cmp ebp, 20
	jae 26f
	jmp 27f
26:
28:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	cmp ebp, 20
	jae 28b
27:
	cmp ebp, 16
	jb 29f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 210f
29:
210:
	cmp ebp, 8
	jae 211f
	jmp 212f
211:
	movq xmm2, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm2, xmm2
	punpckldq xmm3, xmm3
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	add esi, 8
	add edi, 8
	sub ebp, 8
212:
	cmp ebp, 4
	jae 213f
	jmp 214f
213:
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
214:
	mov ebp, ecx
	sub ebp, 8
	jae 215f
	mov ebp, 0
	jmp 216f
215:
216:
	mov esi, DWORD PTR [esp+28]
	add esi, 32
	mov eax, DWORD PTR [esp+36]
	add esi, eax
	sub esi, ecx
	mov edi, DWORD PTR [esp+20]
	add edi, 12
	cmp ebp, 20
	jae 217f
	jmp 218f
217:
219:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	cmp ebp, 20
	jae 219b
218:
	cmp ebp, 16
	jb 220f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 221f
220:
221:
	cmp ebp, 8
	jae 222f
	jmp 223f
222:
	movq xmm2, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm2, xmm2
	punpckldq xmm3, xmm3
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	add esi, 8
	add edi, 8
	sub ebp, 8
223:
	cmp ebp, 4
	jae 224f
	jmp 225f
224:
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
225:
	movdqa xmm2, xmm6
	pmuludq xmm2, xmm7
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
	movd xmm2, eax
	punpcklqdq xmm2, xmm6
	movdqa xmm6, xmm2
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
	jne 25b
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
	cmp ebp, 20
	jae 227f
	jmp 228f
227:
229:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	cmp ebp, 20
	jae 229b
228:
	cmp ebp, 16
	jb 230f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
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
	movq xmm2, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm2, xmm2
	punpckldq xmm3, xmm3
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	add esi, 8
	add edi, 8
	sub ebp, 8
233:
	cmp ebp, 4
	jae 234f
	jmp 235f
234:
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
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
	cmp ebp, 20
	jae 236f
	jmp 237f
236:
238:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	cmp ebp, 20
	jae 238b
237:
	cmp ebp, 16
	jb 239f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
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
	movq xmm2, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm2, xmm2
	punpckldq xmm3, xmm3
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	add esi, 8
	add edi, 8
	sub ebp, 8
242:
	cmp ebp, 4
	jae 243f
	jmp 244f
243:
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
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
	jmp 24f
23:
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
	cmp ebp, 20
	jae 246f
	jmp 247f
246:
248:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	cmp ebp, 20
	jae 248b
247:
	cmp ebp, 16
	jb 249f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
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
	movq xmm2, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm2, xmm2
	punpckldq xmm3, xmm3
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	add esi, 8
	add edi, 8
	sub ebp, 8
252:
	cmp ebp, 4
	jae 253f
	jmp 254f
253:
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
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
	cmp ebp, 20
	jae 259f
	jmp 260f
259:
261:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	cmp ebp, 20
	jae 261b
260:
	cmp ebp, 16
	jb 262f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
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
	movq xmm2, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm2, xmm2
	punpckldq xmm3, xmm3
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	add esi, 8
	add edi, 8
	sub ebp, 8
265:
	cmp ebp, 4
	jae 266f
	jmp 267f
266:
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
267:
	movdqa xmm2, xmm6
	pmuludq xmm2, xmm7
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
	movd xmm2, eax
	punpcklqdq xmm2, xmm6
	movdqa xmm6, xmm2
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
268:
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
	cmp ebp, 20
	jae 269f
	jmp 270f
269:
271:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	cmp ebp, 20
	jae 271b
270:
	cmp ebp, 16
	jb 272f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 273f
272:
273:
	cmp ebp, 8
	jae 274f
	jmp 275f
274:
	movq xmm2, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm2, xmm2
	punpckldq xmm3, xmm3
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	add esi, 8
	add edi, 8
	sub ebp, 8
275:
	cmp ebp, 4
	jae 276f
	jmp 277f
276:
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
277:
	paddq xmm0, xmm0
	paddq xmm1, xmm1
	mov eax, ebx
	add eax, eax
	cmp eax, ecx
	je 278f
	jmp 279f
278:
	mov esi, DWORD PTR [esp+12]
	add esi, ebx
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	pmuludq xmm2, xmm2
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
279:
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
	cmp ebp, 20
	jae 280f
	jmp 281f
280:
282:
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	cmp ebp, 20
	jae 282b
281:
	cmp ebp, 16
	jb 283f
	movdqu xmm2, XMMWORD PTR [esi]
	movdqu xmm3, XMMWORD PTR [edi]
	pshufd xmm4, xmm2, 49
	pshufd xmm5, xmm3, 49
	pmuludq xmm2, xmm3
	pmuludq xmm4, xmm5
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	paddq xmm0, xmm4
	psrlq xmm4, 32
	paddq xmm1, xmm4
	add esi, 16
	add edi, 16
	sub ebp, 16
	jmp 284f
283:
284:
	cmp ebp, 8
	jae 285f
	jmp 286f
285:
	movq xmm2, QWORD PTR [esi]
	movq xmm3, QWORD PTR [edi]
	punpckldq xmm2, xmm2
	punpckldq xmm3, xmm3
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
	add esi, 8
	add edi, 8
	sub ebp, 8
286:
	cmp ebp, 4
	jae 287f
	jmp 288f
287:
	mov eax, DWORD PTR [esi]
	movd xmm2, eax
	mov eax, DWORD PTR [edi]
	movd xmm3, eax
	pmuludq xmm2, xmm3
	paddq xmm0, xmm2
	psrlq xmm2, 32
	paddq xmm1, xmm2
288:
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
	jne 268b
24:
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
289:
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
	jne 289b
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
290:
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
	jne 290b
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
