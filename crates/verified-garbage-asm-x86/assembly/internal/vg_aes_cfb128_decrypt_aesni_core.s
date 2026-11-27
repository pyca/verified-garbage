// The functions of `src/internal/vg_aes_cfb128_decrypt_aesni_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cfb128_decrypt_aesni_core:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	cmp edi, 6
	jb 22f
24:
	movdqu xmm0, XMMWORD PTR [edx]
	movdqu xmm1, XMMWORD PTR [esi]
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm3, XMMWORD PTR [esi+32]
	movdqu xmm4, XMMWORD PTR [esi+48]
	movdqu xmm5, XMMWORD PTR [esi+64]
	movdqu xmm7, XMMWORD PTR [esi+80]
	movdqu XMMWORD PTR [edx], xmm7
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 10
	je 25f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 12
	je 27f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	jmp 28f
27:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
28:
	jmp 26f
25:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
26:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm7, XMMWORD PTR [esi+16]
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu xmm7, XMMWORD PTR [esi+32]
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu xmm7, XMMWORD PTR [esi+48]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [esi+48], xmm3
	movdqu xmm7, XMMWORD PTR [esi+64]
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [esi+64], xmm4
	movdqu xmm7, XMMWORD PTR [esi+80]
	pxor xmm5, xmm7
	movdqu XMMWORD PTR [esi+80], xmm5
	add esi, 96
	sub edi, 6
	cmp edi, 6
	jae 24b
	jmp 23f
22:
23:
	cmp edi, 3
	jb 29f
	movdqu xmm0, XMMWORD PTR [edx]
	movdqu xmm1, XMMWORD PTR [esi]
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm7, XMMWORD PTR [esi+32]
	movdqu XMMWORD PTR [edx], xmm7
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	cmp ecx, 10
	je 211f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	cmp ecx, 12
	je 213f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	jmp 214f
213:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
214:
	jmp 212f
211:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
212:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm7, XMMWORD PTR [esi+16]
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu xmm7, XMMWORD PTR [esi+32]
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [esi+32], xmm2
	add esi, 48
	sub edi, 3
	jmp 210f
29:
210:
	test edi, 2
	je 215f
	movdqu xmm3, XMMWORD PTR [edx]
	movdqu xmm4, XMMWORD PTR [esi]
	movdqu xmm7, XMMWORD PTR [esi+16]
	movdqu XMMWORD PTR [edx], xmm7
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	cmp ecx, 10
	je 217f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	cmp ecx, 12
	je 219f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	jmp 220f
219:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
220:
	jmp 218f
217:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
218:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [esi], xmm3
	movdqu xmm7, XMMWORD PTR [esi+16]
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [esi+16], xmm4
	add esi, 32
	jmp 216f
215:
216:
	test edi, 1
	je 221f
	movdqu xmm5, XMMWORD PTR [edx]
	movdqu xmm7, XMMWORD PTR [esi]
	movdqu XMMWORD PTR [edx], xmm7
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm5, xmm6
	cmp ecx, 10
	je 223f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm5, xmm6
	cmp ecx, 12
	je 225f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm5, xmm6
	jmp 226f
225:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm5, xmm6
226:
	jmp 224f
223:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm5, xmm6
224:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm5, xmm7
	movdqu XMMWORD PTR [esi], xmm5
	add esi, 16
	jmp 222f
221:
222:
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	mov ecx, DWORD PTR [esp+24]
	mov eax, 0
	mov DWORD PTR [ecx+2048], eax
	mov DWORD PTR [ecx+2052], eax
	mov DWORD PTR [ecx+2056], eax
	mov DWORD PTR [ecx+2060], eax
	mov eax, 0
	mov DWORD PTR [ecx+2064], eax
	mov DWORD PTR [ecx+2068], eax
	mov DWORD PTR [ecx+2072], eax
	mov DWORD PTR [ecx+2076], eax
	ret
	.p2align 6
