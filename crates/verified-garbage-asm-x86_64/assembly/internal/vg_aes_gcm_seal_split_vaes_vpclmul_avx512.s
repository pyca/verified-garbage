// The functions of `src/internal/vg_aes_gcm_seal_split_vaes_vpclmul_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_split_vaes_vpclmul_avx512:
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
	or rcx, QWORD PTR [r15+208]
	cmp rcx, 512
	jae 22f
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	add rcx, rdx
	cmp rcx, 32
	jae 24f
	mov rdx, QWORD PTR [r15+208]
	mov rcx, rdx
	shl rcx, 4
	add rcx, rdx
	add rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jb 26f
	mov eax, 1
	jmp 27f
26:
27:
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
	je 28f
	mov rsi, QWORD PTR [r15+224]
	mov rdi, QWORD PTR [r15+200]
	mov rcx, QWORD PTR [r15+192]
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 210f
212:
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
	jne 212b
	jmp 211f
210:
211:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 213f
215:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 215b
	jmp 214f
213:
214:
	cmp r10, rcx
	je 216f
	cmp rcx, 16
	jb 218f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 219f
218:
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
219:
	jmp 217f
216:
217:
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
	jb 221f
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
	jb 223f
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
	jb 225f
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
	jmp 226f
225:
226:
	jmp 224f
223:
224:
	jmp 222f
221:
222:
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
	je 227f
229:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 229b
	jmp 228f
227:
228:
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
230:
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
	je 231f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 12
	je 233f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	jmp 234f
233:
234:
	jmp 232f
231:
232:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	add rdx, 64
	sub r9, 1
	jne 230b
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
	je 235f
237:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 237b
	jmp 236f
235:
236:
	test rcx, 15
	je 238f
	test rcx, 12
	je 240f
	test rcx, 8
	je 242f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 243f
242:
243:
	test rcx, 4
	je 244f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 245f
244:
245:
	test rcx, 3
	je 246f
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
	jmp 247f
246:
247:
	jmp 241f
240:
249:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 249b
241:
	jmp 239f
238:
239:
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
250:
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
	jne 250b
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
	jmp 29f
28:
	cmp rbp, 12
	je 251f
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
	je 253f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 254f
253:
254:
	mov rcx, rbp
	test rcx, rcx
	je 255f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
257:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 257b
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
	jmp 256f
255:
256:
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
	jmp 252f
251:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
252:
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
	je 258f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 259f
258:
259:
	mov rcx, rbp
	test rcx, rcx
	je 260f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
262:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 262b
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
	jmp 261f
260:
261:
	mov rax, QWORD PTR [r15+192]
	shr rax, 4
	test rax, rax
	je 263f
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
	call {vg_aes_gcm_encrypt_blocks_to_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
	jmp 264f
263:
264:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rsi, QWORD PTR [r15+224]
	add rsi, rax
	mov rdi, QWORD PTR [r15+200]
	add rdi, rax
	test rcx, rcx
	je 265f
	mov r10d, 0
267:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 267b
	jmp 266f
265:
266:
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
	je 268f
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
	call {vg_aes_gcm_encrypt_blocks_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 269f
268:
269:
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
	je 270f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 12
	je 272f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm5, zmm5, zmm13
	jmp 273f
272:
273:
	jmp 271f
270:
271:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [r15+1024], zmm5
	vzeroupper
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 274f
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
	je 276f
278:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 278b
	jmp 277f
276:
277:
	test rcx, 15
	je 279f
	test rcx, 12
	je 281f
	test rcx, 8
	je 283f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 284f
283:
284:
	test rcx, 4
	je 285f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 286f
285:
286:
	test rcx, 3
	je 287f
289:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 289b
	jmp 288f
287:
288:
	jmp 282f
281:
290:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 290b
282:
	jmp 280f
279:
280:
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
	jmp 275f
274:
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
275:
	pop rax
29:
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
