// The functions of `src/internal/vg_aes_gcm_open_prepared_aesni_pclmul_avx_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_open_prepared_aesni_pclmul_avx_core:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
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
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 22f
	cmp rbx, 17
	jb 24f
	jmp 25f
24:
	mov ecx, 1
25:
	jmp 23f
22:
23:
	test rcx, rcx
	je 26f
	cmp rbp, 12
	je 28f
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
	je 210f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 211f
210:
211:
	mov rcx, rbp
	test rcx, rcx
	je 212f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
214:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 214b
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
	jmp 213f
212:
213:
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
	jmp 29f
28:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
29:
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
	je 215f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 216f
215:
216:
	mov rcx, rbp
	test rcx, rcx
	je 217f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
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
	jmp 218f
217:
218:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 220f
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
	call {vg_aes_gcm_decrypt_blocks_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 221f
220:
221:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 222f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 223f
222:
223:
	mov rcx, rbp
	test rcx, rcx
	je 224f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
226:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 226b
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
	jmp 225f
224:
225:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
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
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 227f
	mov r10d, 0
229:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 229b
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
228:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 230f
	mov r10d, 0
232:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 232b
	jmp 231f
230:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
231:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 233f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 235f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 236f
235:
236:
	test rbp, rbp
	je 237f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
239:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 239b
	jmp 238f
237:
238:
	jmp 234f
233:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 240f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 241f
240:
241:
234:
	mov rax, QWORD PTR [r15+216]
	jmp 27f
26:
	mov eax, 0
27:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
21:
	ret
20:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
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
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 242f
	cmp rbx, 17
	jb 244f
	jmp 245f
244:
	mov ecx, 1
245:
	jmp 243f
242:
243:
	test rcx, rcx
	je 246f
	mov eax, 0
	cmp rbp, 12
	jne 248f
	mov rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jae 250f
	mov eax, 1
	jmp 251f
250:
251:
	jmp 249f
248:
249:
	test rax, rax
	je 252f
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
	je 254f
	cmp rcx, 5
	je 256f
	cmp rcx, 16
	je 258f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, QWORD PTR [r15+232]
	mov r10d, 0
260:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 260b
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
	jmp 259f
258:
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
259:
	jmp 257f
256:
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
257:
	jmp 255f
254:
255:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 261f
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
	call {vg_aes_gcm_decrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 262f
261:
262:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm3, XMMWORD PTR [r13+272]
	movdqu xmm6, XMMWORD PTR [r13+256]
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 263f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
265:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 265b
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	jmp 264f
263:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
264:
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
	je 266f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 268f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	jmp 269f
268:
269:
	jmp 267f
266:
267:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm5, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [r15+1024], xmm5
	movdqu XMMWORD PTR [r15+1040], xmm7
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+12], esi
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 270f
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
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
	jmp 271f
270:
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
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
271:
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 272f
	mov r10d, 0
274:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 274b
	jmp 273f
272:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
273:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 275f
	mov r10d, 0
277:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 277b
	jmp 276f
275:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
276:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 278f
	mov rcx, QWORD PTR [r15+208]
	test rcx, rcx
	je 280f
	mov rdi, QWORD PTR [r15+200]
	mov rsi, r15
	add rsi, 1040
	mov r10d, 0
282:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 282b
	jmp 281f
280:
281:
	jmp 279f
278:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 283f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 284f
283:
284:
279:
	mov rax, QWORD PTR [r15+216]
	jmp 253f
252:
	cmp rbp, 12
	je 285f
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
	je 287f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 288f
287:
288:
	mov rcx, rbp
	test rcx, rcx
	je 289f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
291:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 291b
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
	jmp 290f
289:
290:
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
	jmp 286f
285:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
286:
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
	je 292f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 293f
292:
293:
	mov rcx, rbp
	test rcx, rcx
	je 294f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
296:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 296b
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
	jmp 295f
294:
295:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 297f
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
	call {vg_aes_gcm_decrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 298f
297:
298:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 299f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 2100f
299:
2100:
	mov rcx, rbp
	test rcx, rcx
	je 2101f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
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
	jmp 2102f
2101:
2102:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
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
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 2104f
	mov r10d, 0
2106:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2106b
	jmp 2105f
2104:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2105:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 2107f
	mov r10d, 0
2109:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2109b
	jmp 2108f
2107:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2108:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 2110f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 2112f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 2113f
2112:
2113:
	test rbp, rbp
	je 2114f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
2116:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2116b
	jmp 2115f
2114:
2115:
	jmp 2111f
2110:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 2117f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 2118f
2117:
2118:
2111:
	mov rax, QWORD PTR [r15+216]
253:
	jmp 247f
246:
	mov eax, 0
247:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	jmp 21b
	.p2align 6
