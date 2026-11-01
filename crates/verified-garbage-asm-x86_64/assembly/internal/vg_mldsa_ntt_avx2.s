// The functions of `src/internal/vg_mldsa_ntt_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_ntt_avx2:
	stmxcsr DWORD PTR [rsi+768]
	mov r11d, DWORD PTR [rsi+768]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rsi+772], eax
	ldmxcsr DWORD PTR [rsi+772]
	lfence
	lea r9, {VG_MLDSA_ZETAS}
	vmovdqu ymm0, YMMWORD PTR [r9]
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+32]
	vmovdqu YMMWORD PTR [rsi+32], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+64]
	vmovdqu YMMWORD PTR [rsi+64], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+96]
	vmovdqu YMMWORD PTR [rsi+96], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+128]
	vmovdqu YMMWORD PTR [rsi+128], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+160]
	vmovdqu YMMWORD PTR [rsi+160], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+192]
	vmovdqu YMMWORD PTR [rsi+192], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+224]
	vmovdqu YMMWORD PTR [rsi+224], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+256]
	vmovdqu YMMWORD PTR [rsi+256], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+288]
	vmovdqu YMMWORD PTR [rsi+288], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+320]
	vmovdqu YMMWORD PTR [rsi+320], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+352]
	vmovdqu YMMWORD PTR [rsi+352], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+384]
	vmovdqu YMMWORD PTR [rsi+384], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+416]
	vmovdqu YMMWORD PTR [rsi+416], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+448]
	vmovdqu YMMWORD PTR [rsi+448], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+480]
	vmovdqu YMMWORD PTR [rsi+480], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+512]
	vmovdqu YMMWORD PTR [rsi+512], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+544]
	vmovdqu YMMWORD PTR [rsi+544], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+576]
	vmovdqu YMMWORD PTR [rsi+576], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+608]
	vmovdqu YMMWORD PTR [rsi+608], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+640]
	vmovdqu YMMWORD PTR [rsi+640], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+672]
	vmovdqu YMMWORD PTR [rsi+672], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+704]
	vmovdqu YMMWORD PTR [rsi+704], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+736]
	vmovdqu YMMWORD PTR [rsi+736], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+768]
	vmovdqu YMMWORD PTR [rsi+768], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+800]
	vmovdqu YMMWORD PTR [rsi+800], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+832]
	vmovdqu YMMWORD PTR [rsi+832], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+864]
	vmovdqu YMMWORD PTR [rsi+864], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+896]
	vmovdqu YMMWORD PTR [rsi+896], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+928]
	vmovdqu YMMWORD PTR [rsi+928], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+960]
	vmovdqu YMMWORD PTR [rsi+960], ymm0
	vmovdqu ymm0, YMMWORD PTR [r9+992]
	vmovdqu YMMWORD PTR [rsi+992], ymm0
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -58728449
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov eax, 16760834
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov rdx, rdi
	mov r8, rsi
	add r8, 4
	mov eax, 1
20:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, 4
	mov ecx, 16
21:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+512]
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm3, ymm3, ymm11
	vpsubd ymm3, ymm3, ymm1
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+512], ymm3
	add rdx, 32
	sub rcx, 1
	jne 21b
	add rdx, 512
	sub rax, 1
	jne 20b
	mov rdx, rdi
	mov r8, rsi
	add r8, 8
	mov eax, 2
22:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, 4
	mov ecx, 8
23:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+256]
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm3, ymm3, ymm11
	vpsubd ymm3, ymm3, ymm1
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+256], ymm3
	add rdx, 32
	sub rcx, 1
	jne 23b
	add rdx, 256
	sub rax, 1
	jne 22b
	mov rdx, rdi
	mov r8, rsi
	add r8, 16
	mov eax, 4
24:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, 4
	mov ecx, 4
25:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+128]
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm3, ymm3, ymm11
	vpsubd ymm3, ymm3, ymm1
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	add rdx, 32
	sub rcx, 1
	jne 25b
	add rdx, 128
	sub rax, 1
	jne 24b
	mov rdx, rdi
	mov r8, rsi
	add r8, 32
	mov eax, 8
26:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, 4
	mov ecx, 2
27:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+64]
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm3, ymm3, ymm11
	vpsubd ymm3, ymm3, ymm1
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+64], ymm3
	add rdx, 32
	sub rcx, 1
	jne 27b
	add rdx, 64
	sub rax, 1
	jne 26b
	mov rdx, rdi
	mov r8, rsi
	add r8, 64
	mov eax, 16
28:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, 4
	mov ecx, 1
29:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm3, ymm3, ymm11
	vpsubd ymm3, ymm3, ymm1
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm3
	add rdx, 32
	sub rcx, 1
	jne 29b
	add rdx, 32
	sub rax, 1
	jne 28b
	mov rdx, rdi
	mov r8, rsi
	add r8, 128
	mov ecx, 16
210:
	vmovdqu ymm4, YMMWORD PTR [rdx]
	vmovdqu ymm5, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 85
	vpshufd ymm13, ymm13, 0
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, 8
	vperm2i128 ymm0, ymm4, ymm5, 32
	vperm2i128 ymm1, ymm4, ymm5, 49
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm3, ymm3, ymm11
	vpsubd ymm3, ymm3, ymm1
	vperm2i128 ymm4, ymm0, ymm3, 32
	vperm2i128 ymm5, ymm0, ymm3, 49
	vmovdqu YMMWORD PTR [rdx], ymm4
	vmovdqu YMMWORD PTR [rdx+32], ymm5
	add rdx, 64
	sub rcx, 1
	jne 210b
	mov rdx, rdi
	mov r8, rsi
	add r8, 256
	mov ecx, 16
211:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 245
	vpshufd ymm13, ymm13, 160
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, 16
	vmovdqa ymm2, ymm0
	vpunpcklqdq ymm0, ymm0, ymm1
	vpunpckhqdq ymm2, ymm2, ymm1
	vmovdqa ymm1, ymm2
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm3, ymm3, ymm11
	vpsubd ymm3, ymm3, ymm1
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm3
	vpunpckhqdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 211b
	mov rdx, rdi
	mov r8, rsi
	add r8, 512
	mov ecx, 16
212:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm2, YMMWORD PTR [rdx+32]
	vmovdqu ymm13, YMMWORD PTR [r8]
	vpermq ymm13, ymm13, 216
	vpshufd ymm12, ymm13, 245
	add r8, 32
	vpshufd ymm0, ymm0, 216
	vpshufd ymm2, ymm2, 216
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm2
	vpunpckhqdq ymm1, ymm1, ymm2
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm3, ymm3, ymm11
	vpsubd ymm3, ymm3, ymm1
	vmovdqa ymm1, ymm0
	vpunpckldq ymm0, ymm0, ymm3
	vpunpckhdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 212b
	mov rdx, rdi
	mov ecx, 32
213:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vpsrld ymm1, ymm0, 23
	vpslld ymm2, ymm1, 23
	vpsubd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 13
	vpaddd ymm0, ymm0, ymm2
	vpsubd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm2, ymm0, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm0, ymm0, ymm2
	vmovdqu YMMWORD PTR [rdx], ymm0
	add rdx, 32
	sub rcx, 1
	jne 213b
	vzeroupper
	lfence
	mov DWORD PTR [rsi+768], r11d
	ldmxcsr DWORD PTR [rsi+768]
	ret
	.p2align 6
