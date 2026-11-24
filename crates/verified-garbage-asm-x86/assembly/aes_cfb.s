// The functions of `src/aes_cfb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cfb128_encrypt_aesni:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+12]
	movdqu xmm0, XMMWORD PTR [edx]
22:
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	cmp ecx, 10
	je 23f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 25f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 26f
25:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
26:
	jmp 24f
23:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
24:
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub ebp, 1
	jne 22b
	mov edx, DWORD PTR [esp+12]
	movdqu XMMWORD PTR [edx], xmm0
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
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-24]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+24]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_decrypt_aesni:
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
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-24]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+24]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_encrypt_final_aesni:
	lea esp, [esp-48]
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	shr esi, 4
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_cfb128_encrypt_aesni_core}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	and eax, 15
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov eax, ebp
	and ebp, 15
	sub eax, ebp
	add esi, eax
22:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+32], xmm0
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-100]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	mov DWORD PTR [esp+96], ecx
	lea esp, [esp+100]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_decrypt_final_aesni:
	lea esp, [esp-48]
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	shr esi, 4
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_cfb128_decrypt_aesni_core}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	and eax, 15
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov eax, ebp
	and ebp, 15
	sub eax, ebp
	add esi, eax
22:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+32], xmm0
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-100]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	mov DWORD PTR [esp+96], ecx
	lea esp, [esp+100]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_encrypt_ssse3:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+24]
	mov edi, eax
	mov eax, 909574400
	mov DWORD PTR [edi], eax
	mov eax, -421015088
	mov DWORD PTR [edi+4], eax
	mov eax, -454700078
	mov DWORD PTR [edi+8], eax
	mov eax, 875889410
	mov DWORD PTR [edi+12], eax
	mov eax, 847858162
	mov DWORD PTR [edi+16], eax
	mov eax, -1925777843
	mov DWORD PTR [edi+20], eax
	mov eax, -96370374
	mov DWORD PTR [edi+24], eax
	mov eax, 1174290053
	mov DWORD PTR [edi+28], eax
	mov eax, 218628480
	mov DWORD PTR [edi+32], eax
	mov eax, 235210255
	mov DWORD PTR [edi+36], eax
	mov eax, 168496130
	mov DWORD PTR [edi+40], eax
	mov eax, 67568393
	mov DWORD PTR [edi+44], eax
	mov eax, 201392768
	mov DWORD PTR [edi+48], eax
	mov eax, 168626952
	mov DWORD PTR [edi+52], eax
	mov eax, 84348420
	mov DWORD PTR [edi+56], eax
	mov eax, 252249603
	mov DWORD PTR [edi+60], eax
	mov eax, 252314880
	mov DWORD PTR [edi+64], eax
	mov eax, 51251460
	mov DWORD PTR [edi+68], eax
	mov eax, 117574920
	mov DWORD PTR [edi+72], eax
	mov eax, 184942860
	mov DWORD PTR [edi+76], eax
	mov eax, 197121
	mov DWORD PTR [edi+80], eax
	mov eax, 67569157
	mov DWORD PTR [edi+84], eax
	mov eax, 134941193
	mov DWORD PTR [edi+88], eax
	mov eax, 202313229
	mov DWORD PTR [edi+92], eax
	mov eax, 287396352
	mov DWORD PTR [edi+96], eax
	mov eax, -1104109588
	mov DWORD PTR [edi+100], eax
	mov eax, -594656259
	mov DWORD PTR [edi+104], eax
	mov eax, 1657646963
	mov DWORD PTR [edi+108], eax
	mov eax, -1600599808
	mov DWORD PTR [edi+112], eax
	mov eax, 2100880820
	mov DWORD PTR [edi+116], eax
	mov eax, -1941608172
	mov DWORD PTR [edi+120], eax
	mov eax, -248717999
	mov DWORD PTR [edi+124], eax
	mov eax, 555497472
	mov DWORD PTR [edi+128], eax
	mov eax, -12721209
	mov DWORD PTR [edi+132], eax
	mov eax, -87942682
	mov DWORD PTR [edi+136], eax
	mov eax, 98295332
	mov DWORD PTR [edi+140], eax
	mov eax, -1475450880
	mov DWORD PTR [edi+144], eax
	mov eax, 1705405197
	mov DWORD PTR [edi+148], eax
	mov eax, -1413234523
	mov DWORD PTR [edi+152], eax
	mov eax, -838611610
	mov DWORD PTR [edi+156], eax
	mov eax, 896203264
	mov DWORD PTR [edi+160], eax
	mov eax, 1096756155
	mov DWORD PTR [edi+164], eax
	mov eax, -467742834
	mov DWORD PTR [edi+168], eax
	mov eax, -1512999792
	mov DWORD PTR [edi+172], eax
	mov eax, -1720286976
	mov DWORD PTR [edi+176], eax
	mov eax, 2096040701
	mov DWORD PTR [edi+180], eax
	mov eax, 311629924
	mov DWORD PTR [edi+184], eax
	mov eax, 1854662135
	mov DWORD PTR [edi+188], eax
	mov eax, 252645135
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	movdqu xmm0, XMMWORD PTR [edi+64]
	movdqu xmm1, XMMWORD PTR [edi+80]
	pshufb xmm0, xmm1
	movdqu XMMWORD PTR [edi+192], xmm0
	pshufb xmm0, xmm1
	pshufb xmm0, xmm1
	movdqu XMMWORD PTR [edi+208], xmm0
	movdqu xmm6, XMMWORD PTR [edi+32]
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, edi
	add ebx, 224
22:
	movdqu xmm0, XMMWORD PTR [esi]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi]
	pshufb xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [edi+16]
	pshufb xmm0, xmm1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [ebx], xmm0
	add esi, 16
	add ebx, 16
	sub ecx, 1
	jne 22b
	mov eax, 1667457891
	movd xmm1, eax
	pshufd xmm1, xmm1, 0
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+12]
	movdqu xmm0, XMMWORD PTR [edx]
23:
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi]
	pshufb xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [edi+16]
	pshufb xmm0, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+224]
	pxor xmm0, xmm1
	mov ebx, edi
	add ebx, 240
	mov ecx, DWORD PTR [esp+8]
	sub ecx, 1
24:
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi+48]
	pshufb xmm2, xmm0
	pxor xmm0, xmm1
	movdqa xmm3, xmm6
	pshufb xmm3, xmm1
	movdqa xmm4, xmm6
	pshufb xmm4, xmm0
	pxor xmm3, xmm2
	pxor xmm4, xmm2
	movdqa xmm2, xmm6
	pshufb xmm2, xmm3
	movdqa xmm5, xmm6
	pshufb xmm5, xmm4
	pxor xmm2, xmm0
	pxor xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+96]
	pshufb xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+112]
	pshufb xmm1, xmm5
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+128]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [edi+144]
	pshufb xmm4, xmm5
	pxor xmm3, xmm4
	movdqu xmm1, XMMWORD PTR [edi+64]
	pshufb xmm3, xmm1
	movdqa xmm4, xmm0
	movdqu xmm1, XMMWORD PTR [edi+192]
	pshufb xmm4, xmm1
	movdqu xmm1, XMMWORD PTR [edi+208]
	pshufb xmm0, xmm1
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx]
	pxor xmm0, xmm2
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+80]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	add ebx, 16
	sub ecx, 1
	jne 24b
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi+48]
	pshufb xmm2, xmm0
	pxor xmm0, xmm1
	movdqa xmm3, xmm6
	pshufb xmm3, xmm1
	movdqa xmm4, xmm6
	pshufb xmm4, xmm0
	pxor xmm3, xmm2
	pxor xmm4, xmm2
	movdqa xmm2, xmm6
	pshufb xmm2, xmm3
	movdqa xmm5, xmm6
	pshufb xmm5, xmm4
	pxor xmm2, xmm0
	pxor xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+160]
	pshufb xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+176]
	pshufb xmm1, xmm5
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pshufb xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub ebp, 1
	jne 23b
	mov edx, DWORD PTR [esp+12]
	movdqu XMMWORD PTR [edx], xmm0
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
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-24]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+24]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_decrypt_ssse3:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
22:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [ebx]
	xor eax, ecx
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [ebx+4]
	xor eax, ecx
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [ebx+8]
	xor eax, ecx
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [ebx+12]
	xor eax, ecx
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [esi]
	xor eax, ecx
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [ebx+4]
	mov ecx, DWORD PTR [esi+4]
	xor eax, ecx
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [ebx+8]
	mov ecx, DWORD PTR [esi+8]
	xor eax, ecx
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [ebx+12]
	mov ecx, DWORD PTR [esi+12]
	xor eax, ecx
	mov DWORD PTR [ebx+12], eax
	add esi, 16
	mov eax, DWORD PTR [esp+20]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [esp+16]
	cmp esi, eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-24]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+24]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_encrypt_final_ssse3:
	lea esp, [esp-48]
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	shr esi, 4
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_cfb128_encrypt_ssse3_core}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	and eax, 15
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov eax, ebp
	and ebp, 15
	sub eax, ebp
	add esi, eax
22:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+32], xmm0
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-100]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	mov DWORD PTR [esp+96], ecx
	lea esp, [esp+100]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_decrypt_final_ssse3:
	lea esp, [esp-48]
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	shr esi, 4
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_cfb128_decrypt_ssse3_core}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	and eax, 15
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov eax, ebp
	and ebp, 15
	sub eax, ebp
	add esi, eax
22:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+32], xmm0
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-100]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	mov DWORD PTR [esp+96], ecx
	lea esp, [esp+100]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_encrypt:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
22:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [ebx]
	xor eax, ecx
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [ebx+4]
	xor eax, ecx
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [ebx+8]
	xor eax, ecx
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [ebx+12]
	xor eax, ecx
	mov DWORD PTR [esi+12], eax
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+8], eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [esi]
	xor eax, ecx
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [ebx+4]
	mov ecx, DWORD PTR [esi+4]
	xor eax, ecx
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [ebx+8]
	mov ecx, DWORD PTR [esi+8]
	xor eax, ecx
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [ebx+12]
	mov ecx, DWORD PTR [esi+12]
	xor eax, ecx
	mov DWORD PTR [ebx+12], eax
	add esi, 16
	mov eax, DWORD PTR [esp+20]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [esp+16]
	cmp esi, eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-24]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+24]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_decrypt:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
22:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [ebx]
	xor eax, ecx
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [ebx+4]
	xor eax, ecx
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [ebx+8]
	xor eax, ecx
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [ebx+12]
	xor eax, ecx
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [esi]
	xor eax, ecx
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [ebx+4]
	mov ecx, DWORD PTR [esi+4]
	xor eax, ecx
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [ebx+8]
	mov ecx, DWORD PTR [esi+8]
	xor eax, ecx
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [ebx+12]
	mov ecx, DWORD PTR [esi+12]
	xor eax, ecx
	mov DWORD PTR [ebx+12], eax
	add esi, 16
	mov eax, DWORD PTR [esp+20]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [esp+16]
	cmp esi, eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-24]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+24]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_encrypt_final:
	lea esp, [esp-48]
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	shr esi, 4
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_cfb128_encrypt_core}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	and eax, 15
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov eax, ebp
	and ebp, 15
	sub eax, ebp
	add esi, eax
22:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+32], xmm0
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-100]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	mov DWORD PTR [esp+96], ecx
	lea esp, [esp+100]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_cfb128_decrypt_final:
	lea esp, [esp-48]
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	shr esi, 4
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_cfb128_decrypt_core}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	and eax, 15
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov eax, ebp
	and ebp, 15
	sub eax, ebp
	add esi, eax
22:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+32], xmm0
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-100]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	mov DWORD PTR [esp+96], ecx
	lea esp, [esp+100]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
