// The functions of `src/internal/vg_mldsa_multiply_add_ntt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_add_ntt:
	lea esp, [esp-12]
	stmxcsr DWORD PTR [esp+4]
	mov eax, 8127
	mov DWORD PTR [esp], eax
	ldmxcsr DWORD PTR [esp]
	lfence
	mov eax, 8380417
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	mov eax, -58728449
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	mov eax, 2365951
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	mov eax, -1
	movd xmm4, eax
	pshufd xmm4, xmm4, 0
	mov eax, -8380417
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, DWORD PTR [esp+16]
	mov ecx, eax
	add ecx, 1024
	mov DWORD PTR [esp+16], ecx
	mov ecx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
20:
	movdqu xmm0, XMMWORD PTR [ecx]
	movdqu xmm1, XMMWORD PTR [edx]
	movdqa xmm2, xmm0
	psrlq xmm2, 32
	pmuludq xmm0, xmm1
	psrlq xmm1, 32
	pmuludq xmm2, xmm1
	movdqa xmm1, xmm0
	pmuludq xmm1, xmm6
	pmuludq xmm1, xmm7
	paddq xmm0, xmm1
	psrlq xmm0, 32
	movdqa xmm1, xmm2
	pmuludq xmm1, xmm6
	pmuludq xmm1, xmm7
	paddq xmm2, xmm1
	por xmm0, xmm2
	movdqa xmm2, xmm0
	psrlq xmm2, 32
	pmuludq xmm0, xmm5
	pmuludq xmm2, xmm5
	movdqa xmm1, xmm0
	pmuludq xmm1, xmm6
	pmuludq xmm1, xmm7
	paddq xmm0, xmm1
	psrlq xmm0, 32
	movdqa xmm1, xmm2
	pmuludq xmm1, xmm6
	pmuludq xmm1, xmm7
	paddq xmm2, xmm1
	por xmm0, xmm2
	paddd xmm0, xmm3
	movdqa xmm1, xmm0
	psrld xmm1, 31
	paddd xmm1, xmm4
	pandn xmm1, xmm7
	paddd xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [eax]
	paddd xmm0, xmm1
	paddd xmm0, xmm3
	movdqa xmm1, xmm0
	psrld xmm1, 31
	paddd xmm1, xmm4
	pandn xmm1, xmm7
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [eax], xmm0
	add eax, 16
	add ecx, 16
	add edx, 16
	cmp eax, DWORD PTR [esp+16]
	jne 20b
	lfence
	ldmxcsr DWORD PTR [esp+4]
	lea esp, [esp+12]
	ret
	.p2align 6
