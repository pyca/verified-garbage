// The functions of `src/internal/vg_aes_gcm_seal_split_prepared_vaes_vpclmul_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_split_prepared_vaes_vpclmul_avx512:
	lea rsp, [rsp-2616]
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+48]
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
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+192], rax
	mov r12, rdx
	mov rbp, rcx
	mov eax, 0
	cmp rbp, 12
	jne 20f
	mov rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jae 22f
	mov rcx, QWORD PTR [r15+208]
	cmp rcx, 256
	jb 24f
	mov eax, 1
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	jmp 21f
20:
21:
	test rax, rax
	je 26f
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
	je 28f
	cmp rcx, 5
	je 210f
	cmp rcx, 16
	je 212f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, QWORD PTR [r15+232]
	mov r10d, 0
214:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 214b
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
	jmp 213f
212:
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
213:
	jmp 211f
210:
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
211:
	jmp 29f
28:
29:
	mov rax, QWORD PTR [r15+192]
	shr rax, 8
	sub rax, 1
	mov rcx, QWORD PTR [r15+208]
	shr rcx, 8
	sub rcx, 1
	cmp rax, rcx
	jb 215f
	mov rax, QWORD PTR [r15+192]
	shr rax, 4
	test rax, rax
	je 217f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+224]
	mov r9, rax
	mov r10, rax
	mov r11, QWORD PTR [r15+200]
	mov rax, r15
	add rax, 448
	push rax
	push r10
	push r11
	call {vg_aes_gcm_encrypt_blocks_to_prepared_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
	jmp 218f
217:
218:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rsi, QWORD PTR [r15+224]
	add rsi, rax
	mov rdi, QWORD PTR [r15+200]
	add rdi, rax
	test rcx, rcx
	je 219f
	mov r10d, 0
221:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 221b
	jmp 220f
219:
220:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+208]
	mov QWORD PTR [r15+216], rcx
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 216f
215:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	shr rax, 8
	shl rax, 8
	sub rcx, rax
	mov rsi, QWORD PTR [r15+224]
	add rsi, rax
	mov rdi, QWORD PTR [r15+200]
	add rdi, rax
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 222f
224:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 224b
	jmp 223f
222:
223:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 225f
227:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 227b
	jmp 226f
225:
226:
	cmp r10, rcx
	je 228f
	cmp rcx, 16
	jb 230f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 231f
230:
232:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 232b
231:
	jmp 229f
228:
229:
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+224]
	mov r9, QWORD PTR [r15+192]
	shr r9, 8
	shl r9, 4
	mov r10, QWORD PTR [r15+200]
	mov rbx, r10
	mov rbp, QWORD PTR [r15+208]
	shr rbp, 8
	shl rbp, 4
	sub rbp, r9
	mov r11, r15
	add r11, 448
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	vinserti128 ymm0, ymm0, xmm0, 1
	vinserti128 ymm1, ymm1, xmm1, 1
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vmovdqu ymm4, YMMWORD PTR [rdi+448]
	vmovdqu ymm5, YMMWORD PTR [rdi+416]
	vmovdqu ymm6, YMMWORD PTR [rdi+384]
	vmovdqu ymm15, YMMWORD PTR [rdi+352]
	vmovdqu ymm14, YMMWORD PTR [rdi+320]
	vmovdqu ymm13, YMMWORD PTR [rdi+288]
	vmovdqu ymm12, YMMWORD PTR [rdi+256]
	vmovdqu YMMWORD PTR [r11], ymm3
	vmovdqu YMMWORD PTR [r11+32], ymm4
	vmovdqu YMMWORD PTR [r11+64], ymm5
	vmovdqu YMMWORD PTR [r11+96], ymm6
	vmovdqu YMMWORD PTR [r11+128], ymm15
	vmovdqu YMMWORD PTR [r11+160], ymm14
	vmovdqu YMMWORD PTR [r11+192], ymm13
	vmovdqu YMMWORD PTR [r11+224], ymm12
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
	movabs rax, 1
	vmovq xmm15, rax
	vmovdqu xmm14, XMMWORD PTR [rdx]
	vpshufb xmm14, xmm14, xmm0
	vpaddd xmm13, xmm14, xmm15
	vinserti128 ymm14, ymm14, xmm13, 1
	movabs rax, 2
	vmovq xmm15, rax
	vinserti128 ymm15, ymm15, xmm15, 1
	sub r8, r10
	mov rax, rdx
	mov rdx, r10
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vpaddd ymm13, ymm14, ymm15
	vshufi32x4 zmm14, zmm14, zmm13, 68
	vpaddd ymm15, ymm15, ymm15
	vshufi32x4 zmm15, zmm15, zmm15, 68
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vshufi32x4 zmm1, zmm1, zmm1, 68
	vmovdqa xmm2, xmm2
	vbroadcasti32x4 zmm16, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm17, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm18, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm19, XMMWORD PTR [rdi+48]
	vbroadcasti32x4 zmm20, XMMWORD PTR [rdi+64]
	vbroadcasti32x4 zmm21, XMMWORD PTR [rdi+80]
	vbroadcasti32x4 zmm22, XMMWORD PTR [rdi+96]
	vbroadcasti32x4 zmm23, XMMWORD PTR [rdi+112]
	vbroadcasti32x4 zmm24, XMMWORD PTR [rdi+128]
	vbroadcasti32x4 zmm25, XMMWORD PTR [rdi+144]
	cmp rsi, 10
	je 233f
	vbroadcasti32x4 zmm26, XMMWORD PTR [rdi+160]
	vbroadcasti32x4 zmm27, XMMWORD PTR [rdi+176]
	cmp rsi, 12
	je 235f
	vbroadcasti32x4 zmm28, XMMWORD PTR [rdi+192]
	vbroadcasti32x4 zmm29, XMMWORD PTR [rdi+208]
	jmp 236f
235:
236:
	jmp 234f
233:
234:
	vbroadcasti32x4 zmm31, XMMWORD PTR [r10]
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 237f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 239f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 240f
239:
240:
	jmp 238f
237:
238:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+64]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+64], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+128]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+128], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+192]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+192], zmm6
	cmp r9, 144
	jb 241f
	vmovdqu ymm12, YMMWORD PTR [rdi+736]
	vmovdqu YMMWORD PTR [r11+256], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+704]
	vmovdqu YMMWORD PTR [r11+288], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+672]
	vmovdqu YMMWORD PTR [r11+320], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+640]
	vmovdqu YMMWORD PTR [r11+352], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+608]
	vmovdqu YMMWORD PTR [r11+384], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+576]
	vmovdqu YMMWORD PTR [r11+416], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+544]
	vmovdqu YMMWORD PTR [r11+448], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+512]
	vmovdqu YMMWORD PTR [r11+480], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+992]
	vmovdqu YMMWORD PTR [r11+512], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+960]
	vmovdqu YMMWORD PTR [r11+544], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+928]
	vmovdqu YMMWORD PTR [r11+576], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+896]
	vmovdqu YMMWORD PTR [r11+608], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+864]
	vmovdqu YMMWORD PTR [r11+640], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+832]
	vmovdqu YMMWORD PTR [r11+672], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+800]
	vmovdqu YMMWORD PTR [r11+704], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+768]
	vmovdqu YMMWORD PTR [r11+736], ymm12
	vmovdqu32 ZMMWORD PTR [r11+832], zmm1
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 243f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 245f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 246f
245:
246:
	jmp 244f
243:
244:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 247f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 249f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 250f
249:
250:
	jmp 248f
247:
248:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+512]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+512], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+576]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+576], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+640]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+640], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+704]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+704], zmm6
251:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+512]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+576]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpxord zmm8, zmm11, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpxord zmm10, zmm11, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpxord zmm9, zmm11, zmm2
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+640]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+704]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 252f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 254f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 255f
254:
255:
	jmp 253f
252:
253:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+768]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+768], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+832]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+832], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+896]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+896], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+960]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+960], zmm6
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+256]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+256]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+320]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+320]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+384]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+384]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+448]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+448]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 256f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 258f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 259f
258:
259:
	jmp 257f
256:
257:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1024]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1024], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1088]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1088], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1152]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1152], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1216]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1216], zmm6
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+512]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+576]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+640]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+704]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 260f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 262f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 263f
262:
263:
	jmp 261f
260:
261:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1280]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1280], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1344]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1344], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1408]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1408], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1472]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1472], zmm6
	add rdx, 768
	sub r9, 48
	cmp r9, 96
	jae 251b
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	add rdx, 256
	sub r9, 16
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	add rdx, 256
	sub r9, 16
	jmp 242f
241:
242:
	cmp r9, 32
	jb 264f
266:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 267f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 269f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 270f
269:
270:
	jmp 268f
267:
268:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	add rdx, 256
	sub r9, 16
	cmp r9, 32
	jae 266b
	jmp 265f
264:
265:
	mov r8, rbx
	add r9, rbp
	cmp r9, 32
	jb 271f
273:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 274f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 276f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 277f
276:
277:
	jmp 275f
274:
275:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	add rdx, 256
	sub r9, 16
	cmp r9, 32
	jae 273b
	jmp 272f
271:
272:
	vpshufb xmm13, xmm14, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+216], rax
	mov rcx, rax
	shr rax, 8
	shl rax, 8
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
216:
	mov rax, QWORD PTR [r15+208]
	cmp rax, 17
	jb 278f
	push rax
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 280f
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
	call {vg_aes_gcm_encrypt_blocks_prepared_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 281f
280:
281:
	mov rax, QWORD PTR [r15+216]
	mov QWORD PTR [r15+192], rax
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
	vmovdqu xmm5, XMMWORD PTR [r14]
	vmovdqu xmm7, XMMWORD PTR [r14+48]
	vinserti128 ymm5, ymm5, xmm7, 1
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 10
	je 282f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 12
	je 284f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm5, zmm5, zmm13
	jmp 285f
284:
285:
	jmp 283f
282:
283:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [r15+1024], zmm5
	vzeroupper
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 286f
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
	je 288f
290:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 290b
	jmp 289f
288:
289:
	test rcx, 15
	je 291f
	test rcx, 12
	je 293f
	test rcx, 8
	je 295f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 296f
295:
296:
	test rcx, 4
	je 297f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 298f
297:
298:
	test rcx, 3
	je 299f
2101:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2101b
	jmp 2100f
299:
2100:
	jmp 294f
293:
2102:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2102b
294:
	jmp 292f
291:
292:
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
	jmp 287f
286:
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
287:
	pop rax
	jmp 279f
278:
	mov rax, QWORD PTR [r15+216]
	mov QWORD PTR [r15+192], rax
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm3, XMMWORD PTR [r13+272]
	movdqu xmm6, XMMWORD PTR [r13+256]
	vmovdqu xmm5, XMMWORD PTR [r14]
	vmovdqu xmm7, XMMWORD PTR [r14+48]
	vinserti128 ymm5, ymm5, xmm7, 1
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 10
	je 2103f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 12
	je 2105f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm5, zmm5, zmm13
	jmp 2106f
2105:
2106:
	jmp 2104f
2103:
2104:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [r15+1024], zmm5
	vzeroupper
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 2107f
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
	je 2109f
2111:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 2111b
	jmp 2110f
2109:
2110:
	test rcx, 15
	je 2112f
	test rcx, 12
	je 2114f
	test rcx, 8
	je 2116f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 2117f
2116:
2117:
	test rcx, 4
	je 2118f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 2119f
2118:
2119:
	test rcx, 3
	je 2120f
2122:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2122b
	jmp 2121f
2120:
2121:
	jmp 2115f
2114:
2123:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2123b
2115:
	jmp 2113f
2112:
2113:
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
	jmp 2108f
2107:
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
2108:
279:
	jmp 27f
26:
	mov eax, 0
	cmp rbp, 12
	jne 2124f
	mov rcx, QWORD PTR [r15+184]
	or rcx, QWORD PTR [r15+208]
	cmp rcx, 512
	jae 2126f
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	add rcx, rdx
	cmp rcx, 32
	jae 2128f
	mov rdx, QWORD PTR [r15+208]
	mov rcx, rdx
	shl rcx, 4
	add rcx, rdx
	add rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jb 2130f
	mov eax, 1
	jmp 2131f
2130:
2131:
	jmp 2129f
2128:
2129:
	jmp 2127f
2126:
2127:
	jmp 2125f
2124:
2125:
	test rax, rax
	je 2132f
	mov rsi, QWORD PTR [r15+224]
	mov rdi, QWORD PTR [r15+200]
	mov rcx, QWORD PTR [r15+192]
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2134f
2136:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 2136b
	jmp 2135f
2134:
2135:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 2137f
2139:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2139b
	jmp 2138f
2137:
2138:
	cmp r10, rcx
	je 2140f
	cmp rcx, 16
	jb 2142f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2143f
2142:
2144:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2144b
2143:
	jmp 2141f
2140:
2141:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov QWORD PTR [r15+272], rcx
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	mov QWORD PTR [r15+280], rdx
	mov rax, rcx
	add rax, rdx
	add rax, 1
	mov r8, rax
	add r8, 3
	shr r8, 2
	shl r8, 2
	mov QWORD PTR [r15+288], r8
	sub r8, rax
	mov QWORD PTR [r15+296], r8
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
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
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
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
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
	mov r11, r15
	add r11, 1536
	vinserti128 ymm8, ymm6, xmm5, 1
	vinserti128 ymm9, ymm4, xmm3, 1
	vshufi32x4 zmm8, zmm8, zmm9, 68
	vmovdqu32 ZMMWORD PTR [r11], zmm8
	vinserti128 ymm0, ymm0, xmm0, 1
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vinserti128 ymm1, ymm1, xmm1, 1
	vshufi32x4 zmm1, zmm1, zmm1, 68
	mov rax, QWORD PTR [r15+288]
	cmp rax, 5
	jb 2145f
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [r11]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+64], zmm10
	cmp rax, 9
	jb 2147f
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [r11]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+128], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+64]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+192], zmm10
	cmp rax, 17
	jb 2149f
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [r11]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+256], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+64]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+320], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+128]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+384], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+192]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+448], zmm10
	jmp 2150f
2149:
2150:
	jmp 2148f
2147:
2148:
	jmp 2146f
2145:
2146:
	vpxord zmm2, zmm2, zmm2
	vmovdqu32 ZMMWORD PTR [r15+512], zmm2
	vmovdqu32 ZMMWORD PTR [r15+576], zmm2
	vmovdqu32 ZMMWORD PTR [r15+640], zmm2
	vmovdqu32 ZMMWORD PTR [r15+704], zmm2
	vmovdqu32 ZMMWORD PTR [r15+768], zmm2
	vmovdqu32 ZMMWORD PTR [r15+832], zmm2
	vmovdqu32 ZMMWORD PTR [r15+896], zmm2
	vmovdqu32 ZMMWORD PTR [r15+960], zmm2
	mov rdi, QWORD PTR [r15+296]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+232]
	mov rcx, QWORD PTR [r15+184]
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2151f
2153:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 2153b
	jmp 2152f
2151:
2152:
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r14
	mov r8, r15
	add r8, 1024
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
	movabs rax, 1
	vmovq xmm15, rax
	vmovdqu xmm14, XMMWORD PTR [rdx]
	vpshufb xmm14, xmm14, xmm0
	vpaddd xmm13, xmm14, xmm15
	vinserti128 ymm14, ymm14, xmm13, 1
	movabs rax, 2
	vmovq xmm15, rax
	vinserti128 ymm15, ymm15, xmm15, 1
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r8
	vpaddd ymm13, ymm14, ymm15
	vshufi32x4 zmm14, zmm14, zmm13, 68
	vpaddd ymm15, ymm15, ymm15
	vshufi32x4 zmm15, zmm15, zmm15, 68
	mov r9, QWORD PTR [r15+280]
	add r9, 4
	shr r9, 2
2154:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 10
	je 2155f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 12
	je 2157f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	jmp 2158f
2157:
2158:
	jmp 2156f
2155:
2156:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	add rdx, 64
	sub r9, 1
	jne 2154b
	mov rdi, QWORD PTR [r15+296]
	add rdi, QWORD PTR [r15+272]
	shl rdi, 4
	add rdi, r15
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
	je 2159f
2161:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 2161b
	jmp 2160f
2159:
2160:
	test rcx, 15
	je 2162f
	test rcx, 12
	je 2164f
	test rcx, 8
	je 2166f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 2167f
2166:
2167:
	test rcx, 4
	je 2168f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 2169f
2168:
2169:
	test rcx, 3
	je 2170f
2172:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2172b
	jmp 2171f
2170:
2171:
	jmp 2165f
2164:
2173:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2173b
2165:
	jmp 2163f
2162:
2163:
	mov rdi, QWORD PTR [r15+288]
	shl rdi, 4
	add rdi, r15
	add rdi, 496
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+208]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rdx, r15
	add rdx, 384
	mov r9, QWORD PTR [r15+288]
	shr r9, 2
	mov r11, r9
	shl r11, 6
	add r11, r15
	add r11, 1344
	vpxord zmm8, zmm8, zmm8
	vpxord zmm9, zmm9, zmm9
	vpxord zmm10, zmm10, zmm10
2174:
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	add rdx, 64
	sub r11, 64
	sub r9, 1
	jne 2174b
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 2133f
2132:
	cmp rbp, 12
	je 2175f
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
	je 2177f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2178f
2177:
2178:
	mov rcx, rbp
	test rcx, rcx
	je 2179f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2181:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2181b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2180f
2179:
2180:
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
	call {vg_ghash_vpclmul}
	jmp 2176f
2175:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
2176:
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
	je 2182f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2183f
2182:
2183:
	mov rcx, rbp
	test rcx, rcx
	je 2184f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2186:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2186b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2185f
2184:
2185:
	mov rax, QWORD PTR [r15+192]
	shr rax, 4
	test rax, rax
	je 2187f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+224]
	mov r9, rax
	mov r10, rax
	mov r11, QWORD PTR [r15+200]
	mov rax, r15
	add rax, 448
	push rax
	push r10
	push r11
	call {vg_aes_gcm_encrypt_blocks_to_prepared_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
	jmp 2188f
2187:
2188:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rsi, QWORD PTR [r15+224]
	add rsi, rax
	mov rdi, QWORD PTR [r15+200]
	add rdi, rax
	test rcx, rcx
	je 2189f
	mov r10d, 0
2191:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2191b
	jmp 2190f
2189:
2190:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+208]
	mov QWORD PTR [r15+216], rcx
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	push rax
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 2192f
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
	call {vg_aes_gcm_encrypt_blocks_prepared_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 2193f
2192:
2193:
	mov rax, QWORD PTR [r15+216]
	mov QWORD PTR [r15+192], rax
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
	vmovdqu xmm5, XMMWORD PTR [r14]
	vmovdqu xmm7, XMMWORD PTR [r14+48]
	vinserti128 ymm5, ymm5, xmm7, 1
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 10
	je 2194f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 12
	je 2196f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm5, zmm5, zmm13
	jmp 2197f
2196:
2197:
	jmp 2195f
2194:
2195:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [r15+1024], zmm5
	vzeroupper
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 2198f
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
	je 2200f
2202:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 2202b
	jmp 2201f
2200:
2201:
	test rcx, 15
	je 2203f
	test rcx, 12
	je 2205f
	test rcx, 8
	je 2207f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 2208f
2207:
2208:
	test rcx, 4
	je 2209f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 2210f
2209:
2210:
	test rcx, 3
	je 2211f
2213:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2213b
	jmp 2212f
2211:
2212:
	jmp 2206f
2205:
2214:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2214b
2206:
	jmp 2204f
2203:
2204:
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
	jmp 2199f
2198:
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
2199:
	pop rax
2133:
27:
	mov rdi, QWORD PTR [rsp+40]
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
	lea rsp, [rsp+2616]
	ret
	.p2align 6
