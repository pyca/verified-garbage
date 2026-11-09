// The functions of `src/internal/vg_aes_decrypt_blocks_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_decrypt_blocks_aesni:
	mov edx, DWORD PTR [esp+20]
	mov DWORD PTR [edx], esi
	mov DWORD PTR [edx+4], edi
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+16]
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
	je 20f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+160], xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+176], xmm6
	cmp ecx, 12
	je 22f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+192], xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+208], xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	movdqu XMMWORD PTR [edx+224], xmm6
	jmp 23f
22:
	movdqu xmm6, XMMWORD PTR [eax+192]
	movdqu XMMWORD PTR [edx+224], xmm6
23:
	jmp 21f
20:
	movdqu xmm6, XMMWORD PTR [eax+160]
	movdqu XMMWORD PTR [edx+224], xmm6
21:
	cmp edi, 6
	jb 24f
26:
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm1, XMMWORD PTR [esi+16]
	movdqu xmm2, XMMWORD PTR [esi+32]
	movdqu xmm3, XMMWORD PTR [esi+48]
	movdqu xmm4, XMMWORD PTR [esi+64]
	movdqu xmm5, XMMWORD PTR [esi+80]
	movdqu xmm6, XMMWORD PTR [edx+224]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	cmp ecx, 10
	je 27f
	cmp ecx, 12
	je 29f
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
	jmp 210f
29:
210:
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
	jmp 28f
27:
28:
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
	movdqu XMMWORD PTR [esi], xmm0
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu XMMWORD PTR [esi+48], xmm3
	movdqu XMMWORD PTR [esi+64], xmm4
	movdqu XMMWORD PTR [esi+80], xmm5
	add esi, 96
	sub edi, 6
	cmp edi, 6
	jae 26b
	jmp 25f
24:
25:
	test edi, edi
	je 211f
213:
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm6, XMMWORD PTR [edx+224]
	pxor xmm0, xmm6
	cmp ecx, 10
	je 214f
	cmp ecx, 12
	je 216f
	movdqu xmm6, XMMWORD PTR [edx+208]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+192]
	aesdec xmm0, xmm6
	jmp 217f
216:
217:
	movdqu xmm6, XMMWORD PTR [edx+176]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	aesdec xmm0, xmm6
	jmp 215f
214:
215:
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
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub edi, 1
	jne 213b
	jmp 212f
211:
212:
	mov esi, DWORD PTR [edx]
	mov edi, DWORD PTR [edx+4]
	ret
	.p2align 6
