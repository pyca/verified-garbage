// The functions of `src/internal/vg_aes_xts_decrypt_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_decrypt_aesni:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
	mov edx, DWORD PTR [esp+24]
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	mov eax, 134
	movd xmm7, eax
	movdqa xmm5, xmm6
	psrld xmm5, 31
	pxor xmm7, xmm5
	movdqu XMMWORD PTR [edx+352], xmm6
	movdqu XMMWORD PTR [edx+368], xmm7
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+16], xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+32], xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+48], xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+64], xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+80], xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+96], xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+112], xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+128], xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+144], xmm6
	cmp ecx, 10
	je 22f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+160], xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+176], xmm6
	cmp ecx, 12
	je 24f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+192], xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+208], xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	movdqu XMMWORD PTR [edx+224], xmm6
	jmp 25f
24:
	movdqu xmm6, XMMWORD PTR [eax+192]
	movdqu XMMWORD PTR [edx+224], xmm6
25:
	jmp 23f
22:
	movdqu xmm6, XMMWORD PTR [eax+160]
	movdqu XMMWORD PTR [edx+224], xmm6
23:
	mov ebp, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+20]
	movdqu xmm7, XMMWORD PTR [ebp]
	cmp edi, 6
	jb 26f
28:
	movdqu xmm5, XMMWORD PTR [edx+352]
	movdqu xmm6, XMMWORD PTR [edx+368]
	movdqu XMMWORD PTR [edx+256], xmm7
	pshufd xmm4, xmm7, 147
	psrld xmm4, 31
	paddd xmm4, xmm5
	pandn xmm4, xmm6
	paddd xmm7, xmm7
	pxor xmm7, xmm4
	movdqu XMMWORD PTR [edx+272], xmm7
	pshufd xmm4, xmm7, 147
	psrld xmm4, 31
	paddd xmm4, xmm5
	pandn xmm4, xmm6
	paddd xmm7, xmm7
	pxor xmm7, xmm4
	movdqu XMMWORD PTR [edx+288], xmm7
	pshufd xmm4, xmm7, 147
	psrld xmm4, 31
	paddd xmm4, xmm5
	pandn xmm4, xmm6
	paddd xmm7, xmm7
	pxor xmm7, xmm4
	movdqu XMMWORD PTR [edx+304], xmm7
	pshufd xmm4, xmm7, 147
	psrld xmm4, 31
	paddd xmm4, xmm5
	pandn xmm4, xmm6
	paddd xmm7, xmm7
	pxor xmm7, xmm4
	movdqu XMMWORD PTR [edx+320], xmm7
	pshufd xmm4, xmm7, 147
	psrld xmm4, 31
	paddd xmm4, xmm5
	pandn xmm4, xmm6
	paddd xmm7, xmm7
	pxor xmm7, xmm4
	movdqu XMMWORD PTR [edx+336], xmm7
	pshufd xmm4, xmm7, 147
	psrld xmm4, 31
	paddd xmm4, xmm5
	pandn xmm4, xmm6
	paddd xmm7, xmm7
	pxor xmm7, xmm4
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm6, XMMWORD PTR [edx+256]
	pxor xmm0, xmm6
	movdqu xmm1, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edx+272]
	pxor xmm1, xmm6
	movdqu xmm2, XMMWORD PTR [esi+32]
	movdqu xmm6, XMMWORD PTR [edx+288]
	pxor xmm2, xmm6
	movdqu xmm3, XMMWORD PTR [esi+48]
	movdqu xmm6, XMMWORD PTR [edx+304]
	pxor xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+64]
	movdqu xmm6, XMMWORD PTR [edx+320]
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [esi+80]
	movdqu xmm6, XMMWORD PTR [edx+336]
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	cmp ecx, 10
	je 29f
	cmp ecx, 12
	je 211f
	movdqu xmm6, XMMWORD PTR [edx+208]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+192]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	jmp 212f
211:
212:
	movdqu xmm6, XMMWORD PTR [edx+176]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	jmp 210f
29:
210:
	movdqu xmm6, XMMWORD PTR [edx+144]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+96]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+64]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+48]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+32]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	aesdec xmm0, xmm6
	aesdec xmm1, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax]
	aesdeclast xmm0, xmm6
	aesdeclast xmm1, xmm6
	aesdeclast xmm2, xmm6
	aesdeclast xmm3, xmm6
	aesdeclast xmm4, xmm6
	aesdeclast xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm6, XMMWORD PTR [edx+272]
	pxor xmm1, xmm6
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu xmm6, XMMWORD PTR [edx+288]
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu xmm6, XMMWORD PTR [edx+304]
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [esi+48], xmm3
	movdqu xmm6, XMMWORD PTR [edx+320]
	pxor xmm4, xmm6
	movdqu XMMWORD PTR [esi+64], xmm4
	movdqu xmm6, XMMWORD PTR [edx+336]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [esi+80], xmm5
	add esi, 96
	sub edi, 6
	cmp edi, 6
	jae 28b
	jmp 27f
26:
27:
	test edi, edi
	je 213f
215:
	movdqu xmm5, XMMWORD PTR [edx+352]
	movdqu xmm6, XMMWORD PTR [edx+368]
	movdqu XMMWORD PTR [edx+256], xmm7
	pshufd xmm4, xmm7, 147
	psrld xmm4, 31
	paddd xmm4, xmm5
	pandn xmm4, xmm6
	paddd xmm7, xmm7
	pxor xmm7, xmm4
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm6, XMMWORD PTR [edx+256]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pxor xmm0, xmm6
	cmp ecx, 10
	je 216f
	cmp ecx, 12
	je 218f
	movdqu xmm6, XMMWORD PTR [edx+208]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+192]
	aesdec xmm0, xmm6
	jmp 219f
218:
219:
	movdqu xmm6, XMMWORD PTR [edx+176]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	aesdec xmm0, xmm6
	jmp 217f
216:
217:
	movdqu xmm6, XMMWORD PTR [edx+144]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+96]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+64]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+48]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+32]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax]
	aesdeclast xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub edi, 1
	jne 215b
	jmp 214f
213:
214:
	movdqu XMMWORD PTR [ebp], xmm7
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	ret
	.p2align 6
