// The functions of `src/internal/vg_aes_gcm_seal_prepared16_aesni_pclmul_avx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_prepared16_aesni_pclmul_avx:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov eax, 0
	cmp rbp, 12
	jne 20f
	mov rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jae 22f
	mov eax, 1
	jmp 23f
22:
23:
	jmp 21f
20:
21:
	test rax, rax
	je 24f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rcx, QWORD PTR [r15+184]
	test rcx, rcx
	je 26f
	cmp rcx, 5
	je 28f
	cmp rcx, 16
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, QWORD PTR [r15+232]
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r15+96]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
	jmp 211f
210:
	mov rsi, QWORD PTR [r15+232]
	movdqu xmm7, XMMWORD PTR [rsi]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
211:
	jmp 29f
28:
	mov rsi, QWORD PTR [r15+232]
	mov eax, DWORD PTR [rsi]
	movzx r10d, BYTE PTR [rsi+4]
	shl r10, 32
	add rax, r10
	movq xmm7, rax
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
29:
	jmp 27f
26:
27:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 213f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 214f
213:
214:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm3, XMMWORD PTR [r13+272]
	movdqu xmm6, XMMWORD PTR [r13+256]
	movdqu xmm5, XMMWORD PTR [r14]
	movdqu xmm7, XMMWORD PTR [r14+48]
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm5, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 215f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 217f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	jmp 218f
217:
218:
	jmp 216f
215:
216:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm5, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [r15+1024], xmm5
	movdqu XMMWORD PTR [r15+1040], xmm7
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 219f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 221f
223:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 223b
	jmp 222f
221:
222:
	test rcx, 15
	je 224f
	test rcx, 12
	je 226f
	test rcx, 8
	je 228f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 229f
228:
229:
	test rcx, 4
	je 230f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 231f
230:
231:
	test rcx, 3
	je 232f
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	jmp 233f
232:
233:
	jmp 227f
226:
235:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 235b
227:
	jmp 225f
224:
225:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 220f
219:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
220:
	jmp 25f
24:
	cmp rbp, 12
	je 236f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 238f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 239f
238:
239:
	mov rcx, rbp
	test rcx, rcx
	je 240f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
242:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 242b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 241f
240:
241:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 237f
236:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
237:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 243f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 244f
243:
244:
	mov rcx, rbp
	test rcx, rcx
	je 245f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
247:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 247b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 246f
245:
246:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 248f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 249f
248:
249:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r13+240]
	pshufb xmm7, xmm0
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm13, XMMWORD PTR [rax+32]
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	movdqu xmm5, XMMWORD PTR [r14]
	movdqu xmm7, XMMWORD PTR [r14+48]
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm5, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 250f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 252f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	jmp 253f
252:
253:
	jmp 251f
250:
251:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm5, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [r15+1024], xmm5
	movdqu XMMWORD PTR [r15+1040], xmm7
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 254f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 256f
258:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 258b
	jmp 257f
256:
257:
	test rcx, 15
	je 259f
	test rcx, 12
	je 261f
	test rcx, 8
	je 263f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 264f
263:
264:
	test rcx, 4
	je 265f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 266f
265:
266:
	test rcx, 3
	je 267f
269:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 269b
	jmp 268f
267:
268:
	jmp 262f
261:
270:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 270b
262:
	jmp 260f
259:
260:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 255f
254:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
255:
25:
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	ret
	.p2align 6
