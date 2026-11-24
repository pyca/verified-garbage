// The functions of `src/internal/vg_aes_gcm_bounded_seal_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_bounded_seal_avx512:
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
	mov rbp, r10
	mov r12, r11
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	vinserti128 ymm0, ymm0, xmm0, 1
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vinserti128 ymm1, ymm1, xmm1, 1
	vshufi32x4 zmm1, zmm1, zmm1, 68
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
	je 20f
22:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 22b
	jmp 21f
20:
21:
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
23:
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
	je 24f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 12
	je 26f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	jmp 27f
26:
27:
	jmp 25f
24:
25:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	add rdx, 64
	sub r9, 1
	jne 23b
	mov rdi, QWORD PTR [r15+296]
	add rdi, QWORD PTR [r15+272]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r11, rcx
	mov rcx, rbp
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 28f
210:
	vmovdqu xmm4, XMMWORD PTR [rbx+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 210b
	jmp 29f
28:
29:
	test rcx, 15
	je 211f
	test rcx, 12
	je 213f
	test rcx, 8
	je 215f
	mov rax, QWORD PTR [rbx+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 216f
215:
216:
	test rcx, 4
	je 217f
	mov eax, DWORD PTR [rbx+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 218f
217:
218:
	test rcx, 3
	je 219f
221:
	movzx eax, BYTE PTR [rbx+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 221b
	jmp 220f
219:
220:
	jmp 214f
213:
222:
	movzx eax, BYTE PTR [rbx+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
214:
	jmp 212f
211:
212:
	mov rcx, r11
	sub rcx, rbp
	je 223f
	mov rbx, r12
	add rsi, rbp
	add rdx, rbp
	add rdi, rbp
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 225f
227:
	vmovdqu xmm4, XMMWORD PTR [rbx+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 227b
	jmp 226f
225:
226:
	test rcx, 15
	je 228f
	test rcx, 12
	je 230f
	test rcx, 8
	je 232f
	mov rax, QWORD PTR [rbx+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 233f
232:
233:
	test rcx, 4
	je 234f
	mov eax, DWORD PTR [rbx+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 235f
234:
235:
	test rcx, 3
	je 236f
238:
	movzx eax, BYTE PTR [rbx+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 231f
230:
239:
	movzx eax, BYTE PTR [rbx+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 239b
231:
	jmp 229f
228:
229:
	jmp 224f
223:
224:
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
	add r11, r13
	add r11, 64
	vpxord zmm8, zmm8, zmm8
	vpxord zmm9, zmm9, zmm9
	vpxord zmm10, zmm10, zmm10
240:
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vshufi32x4 zmm12, zmm12, zmm12, 78
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
	jne 240b
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
	ret
	.p2align 6
