// The functions of `src/internal/vg_mldsa_multiply_ntt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_ntt:
	mov r8, rdi
	movdqu xmm6, XMMWORD PTR [rdi+1008]
	stmxcsr DWORD PTR [r8+1016]
	mov r11d, DWORD PTR [r8+1016]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [r8+1020], eax
	ldmxcsr DWORD PTR [r8+1020]
	lfence
	mov eax, 8380417
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov eax, -58728449
	movq xmm14, rax
	pshufd xmm14, xmm14, 0
	mov eax, 2365951
	movq xmm11, rax
	pshufd xmm11, xmm11, 0
	mov ecx, 63
20:
	movdqu xmm3, XMMWORD PTR [rsi]
	movdqu xmm13, XMMWORD PTR [rdx]
	movdqu xmm5, XMMWORD PTR [rdi]
	pshufd xmm12, xmm13, 245
	pshufd xmm4, xmm3, 245
	pmuludq xmm3, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm3
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm3, xmm2
	psrlq xmm3, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm3, xmm4
	pshufd xmm4, xmm3, 245
	pmuludq xmm3, xmm11
	pmuludq xmm4, xmm11
	movdqa xmm2, xmm3
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm3, xmm2
	psrlq xmm3, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm3, xmm4
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdi], xmm3
	add rdi, 16
	add rsi, 16
	add rdx, 16
	sub rcx, 1
	jne 20b
	movdqu xmm3, XMMWORD PTR [rsi]
	movdqu xmm13, XMMWORD PTR [rdx]
	movdqa xmm5, xmm6
	pshufd xmm12, xmm13, 245
	pshufd xmm4, xmm3, 245
	pmuludq xmm3, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm3
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm3, xmm2
	psrlq xmm3, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm3, xmm4
	pshufd xmm4, xmm3, 245
	pmuludq xmm3, xmm11
	pmuludq xmm4, xmm11
	movdqa xmm2, xmm3
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm3, xmm2
	psrlq xmm3, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm3, xmm4
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	lfence
	mov DWORD PTR [r8+1016], r11d
	ldmxcsr DWORD PTR [r8+1016]
	movdqu XMMWORD PTR [rdi], xmm3
	ret
	.p2align 6
