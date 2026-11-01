// The functions of `src/internal/vg_mldsa_dot_inverse4.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_dot_inverse4:
	mov r10, rsi
	mov rsi, rcx
	stmxcsr DWORD PTR [rsi+768]
	mov r11d, DWORD PTR [rsi+768]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rsi+772], eax
	ldmxcsr DWORD PTR [rsi+772]
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
	mov r8, rdi
	mov ecx, 64
20:
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	movdqu xmm0, XMMWORD PTR [r10]
	movdqu xmm1, XMMWORD PTR [rdx]
	movdqa xmm2, xmm0
	psrlq xmm2, 32
	movdqa xmm3, xmm1
	psrlq xmm3, 32
	pmuludq xmm2, xmm3
	pmuludq xmm0, xmm1
	paddq xmm5, xmm0
	paddq xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [r10+1024]
	movdqu xmm1, XMMWORD PTR [rdx+1024]
	movdqa xmm2, xmm0
	psrlq xmm2, 32
	movdqa xmm3, xmm1
	psrlq xmm3, 32
	pmuludq xmm2, xmm3
	pmuludq xmm0, xmm1
	paddq xmm5, xmm0
	paddq xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [r10+2048]
	movdqu xmm1, XMMWORD PTR [rdx+2048]
	movdqa xmm2, xmm0
	psrlq xmm2, 32
	movdqa xmm3, xmm1
	psrlq xmm3, 32
	pmuludq xmm2, xmm3
	pmuludq xmm0, xmm1
	paddq xmm5, xmm0
	paddq xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [r10+3072]
	movdqu xmm1, XMMWORD PTR [rdx+3072]
	movdqa xmm2, xmm0
	psrlq xmm2, 32
	movdqa xmm3, xmm1
	psrlq xmm3, 32
	pmuludq xmm2, xmm3
	pmuludq xmm0, xmm1
	paddq xmm5, xmm0
	paddq xmm6, xmm2
	movdqa xmm2, xmm5
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm5, xmm2
	psrlq xmm5, 32
	movdqa xmm2, xmm6
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm6, xmm2
	por xmm5, xmm6
	psubd xmm5, xmm15
	movdqa xmm2, xmm5
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm5, xmm2
	pshufd xmm4, xmm5, 245
	pmuludq xmm5, xmm11
	pmuludq xmm4, xmm11
	movdqa xmm2, xmm5
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm5, xmm2
	psrlq xmm5, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm5, xmm4
	psubd xmm5, xmm15
	movdqa xmm2, xmm5
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm5, xmm2
	movdqu XMMWORD PTR [r8], xmm5
	add r8, 16
	add r10, 16
	add rdx, 16
	sub rcx, 1
	jne 20b
	lea r9, {VG_MLDSA_ZETAS}
	movdqu xmm0, XMMWORD PTR [r9]
	movdqu XMMWORD PTR [rsi], xmm0
	movdqu xmm0, XMMWORD PTR [r9+16]
	movdqu XMMWORD PTR [rsi+16], xmm0
	movdqu xmm0, XMMWORD PTR [r9+32]
	movdqu XMMWORD PTR [rsi+32], xmm0
	movdqu xmm0, XMMWORD PTR [r9+48]
	movdqu XMMWORD PTR [rsi+48], xmm0
	movdqu xmm0, XMMWORD PTR [r9+64]
	movdqu XMMWORD PTR [rsi+64], xmm0
	movdqu xmm0, XMMWORD PTR [r9+80]
	movdqu XMMWORD PTR [rsi+80], xmm0
	movdqu xmm0, XMMWORD PTR [r9+96]
	movdqu XMMWORD PTR [rsi+96], xmm0
	movdqu xmm0, XMMWORD PTR [r9+112]
	movdqu XMMWORD PTR [rsi+112], xmm0
	movdqu xmm0, XMMWORD PTR [r9+128]
	movdqu XMMWORD PTR [rsi+128], xmm0
	movdqu xmm0, XMMWORD PTR [r9+144]
	movdqu XMMWORD PTR [rsi+144], xmm0
	movdqu xmm0, XMMWORD PTR [r9+160]
	movdqu XMMWORD PTR [rsi+160], xmm0
	movdqu xmm0, XMMWORD PTR [r9+176]
	movdqu XMMWORD PTR [rsi+176], xmm0
	movdqu xmm0, XMMWORD PTR [r9+192]
	movdqu XMMWORD PTR [rsi+192], xmm0
	movdqu xmm0, XMMWORD PTR [r9+208]
	movdqu XMMWORD PTR [rsi+208], xmm0
	movdqu xmm0, XMMWORD PTR [r9+224]
	movdqu XMMWORD PTR [rsi+224], xmm0
	movdqu xmm0, XMMWORD PTR [r9+240]
	movdqu XMMWORD PTR [rsi+240], xmm0
	movdqu xmm0, XMMWORD PTR [r9+256]
	movdqu XMMWORD PTR [rsi+256], xmm0
	movdqu xmm0, XMMWORD PTR [r9+272]
	movdqu XMMWORD PTR [rsi+272], xmm0
	movdqu xmm0, XMMWORD PTR [r9+288]
	movdqu XMMWORD PTR [rsi+288], xmm0
	movdqu xmm0, XMMWORD PTR [r9+304]
	movdqu XMMWORD PTR [rsi+304], xmm0
	movdqu xmm0, XMMWORD PTR [r9+320]
	movdqu XMMWORD PTR [rsi+320], xmm0
	movdqu xmm0, XMMWORD PTR [r9+336]
	movdqu XMMWORD PTR [rsi+336], xmm0
	movdqu xmm0, XMMWORD PTR [r9+352]
	movdqu XMMWORD PTR [rsi+352], xmm0
	movdqu xmm0, XMMWORD PTR [r9+368]
	movdqu XMMWORD PTR [rsi+368], xmm0
	movdqu xmm0, XMMWORD PTR [r9+384]
	movdqu XMMWORD PTR [rsi+384], xmm0
	movdqu xmm0, XMMWORD PTR [r9+400]
	movdqu XMMWORD PTR [rsi+400], xmm0
	movdqu xmm0, XMMWORD PTR [r9+416]
	movdqu XMMWORD PTR [rsi+416], xmm0
	movdqu xmm0, XMMWORD PTR [r9+432]
	movdqu XMMWORD PTR [rsi+432], xmm0
	movdqu xmm0, XMMWORD PTR [r9+448]
	movdqu XMMWORD PTR [rsi+448], xmm0
	movdqu xmm0, XMMWORD PTR [r9+464]
	movdqu XMMWORD PTR [rsi+464], xmm0
	movdqu xmm0, XMMWORD PTR [r9+480]
	movdqu XMMWORD PTR [rsi+480], xmm0
	movdqu xmm0, XMMWORD PTR [r9+496]
	movdqu XMMWORD PTR [rsi+496], xmm0
	movdqu xmm0, XMMWORD PTR [r9+512]
	movdqu XMMWORD PTR [rsi+512], xmm0
	movdqu xmm0, XMMWORD PTR [r9+528]
	movdqu XMMWORD PTR [rsi+528], xmm0
	movdqu xmm0, XMMWORD PTR [r9+544]
	movdqu XMMWORD PTR [rsi+544], xmm0
	movdqu xmm0, XMMWORD PTR [r9+560]
	movdqu XMMWORD PTR [rsi+560], xmm0
	movdqu xmm0, XMMWORD PTR [r9+576]
	movdqu XMMWORD PTR [rsi+576], xmm0
	movdqu xmm0, XMMWORD PTR [r9+592]
	movdqu XMMWORD PTR [rsi+592], xmm0
	movdqu xmm0, XMMWORD PTR [r9+608]
	movdqu XMMWORD PTR [rsi+608], xmm0
	movdqu xmm0, XMMWORD PTR [r9+624]
	movdqu XMMWORD PTR [rsi+624], xmm0
	movdqu xmm0, XMMWORD PTR [r9+640]
	movdqu XMMWORD PTR [rsi+640], xmm0
	movdqu xmm0, XMMWORD PTR [r9+656]
	movdqu XMMWORD PTR [rsi+656], xmm0
	movdqu xmm0, XMMWORD PTR [r9+672]
	movdqu XMMWORD PTR [rsi+672], xmm0
	movdqu xmm0, XMMWORD PTR [r9+688]
	movdqu XMMWORD PTR [rsi+688], xmm0
	movdqu xmm0, XMMWORD PTR [r9+704]
	movdqu XMMWORD PTR [rsi+704], xmm0
	movdqu xmm0, XMMWORD PTR [r9+720]
	movdqu XMMWORD PTR [rsi+720], xmm0
	movdqu xmm0, XMMWORD PTR [r9+736]
	movdqu XMMWORD PTR [rsi+736], xmm0
	movdqu xmm0, XMMWORD PTR [r9+752]
	movdqu XMMWORD PTR [rsi+752], xmm0
	movdqu xmm0, XMMWORD PTR [r9+768]
	movdqu XMMWORD PTR [rsi+768], xmm0
	movdqu xmm0, XMMWORD PTR [r9+784]
	movdqu XMMWORD PTR [rsi+784], xmm0
	movdqu xmm0, XMMWORD PTR [r9+800]
	movdqu XMMWORD PTR [rsi+800], xmm0
	movdqu xmm0, XMMWORD PTR [r9+816]
	movdqu XMMWORD PTR [rsi+816], xmm0
	movdqu xmm0, XMMWORD PTR [r9+832]
	movdqu XMMWORD PTR [rsi+832], xmm0
	movdqu xmm0, XMMWORD PTR [r9+848]
	movdqu XMMWORD PTR [rsi+848], xmm0
	movdqu xmm0, XMMWORD PTR [r9+864]
	movdqu XMMWORD PTR [rsi+864], xmm0
	movdqu xmm0, XMMWORD PTR [r9+880]
	movdqu XMMWORD PTR [rsi+880], xmm0
	movdqu xmm0, XMMWORD PTR [r9+896]
	movdqu XMMWORD PTR [rsi+896], xmm0
	movdqu xmm0, XMMWORD PTR [r9+912]
	movdqu XMMWORD PTR [rsi+912], xmm0
	movdqu xmm0, XMMWORD PTR [r9+928]
	movdqu XMMWORD PTR [rsi+928], xmm0
	movdqu xmm0, XMMWORD PTR [r9+944]
	movdqu XMMWORD PTR [rsi+944], xmm0
	movdqu xmm0, XMMWORD PTR [r9+960]
	movdqu XMMWORD PTR [rsi+960], xmm0
	movdqu xmm0, XMMWORD PTR [r9+976]
	movdqu XMMWORD PTR [rsi+976], xmm0
	movdqu xmm0, XMMWORD PTR [r9+992]
	movdqu XMMWORD PTR [rsi+992], xmm0
	movdqu xmm0, XMMWORD PTR [r9+1008]
	movdqu XMMWORD PTR [rsi+1008], xmm0
	mov eax, 8380417
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov eax, -58728449
	movq xmm14, rax
	pshufd xmm14, xmm14, 0
	mov rdx, rdi
	mov r8, rsi
	add r8, 1008
	mov ecx, 32
21:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm2, XMMWORD PTR [rdx+16]
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 27
	pshufd xmm12, xmm13, 245
	add r8, -16
	pshufd xmm0, xmm0, 216
	pshufd xmm2, xmm2, 216
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm3, xmm1
	psubd xmm3, xmm0
	paddd xmm3, xmm15
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
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
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqa xmm1, xmm0
	punpckldq xmm0, xmm3
	punpckhdq xmm1, xmm3
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm1
	add rdx, 32
	sub rcx, 1
	jne 21b
	mov rdx, rdi
	mov r8, rsi
	add r8, 504
	mov ecx, 32
22:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 5
	pshufd xmm12, xmm13, 245
	add r8, -8
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm1, xmm2
	movdqa xmm3, xmm1
	psubd xmm3, xmm0
	paddd xmm3, xmm15
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
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
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm3
	punpckhqdq xmm1, xmm3
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm1
	add rdx, 32
	sub rcx, 1
	jne 22b
	mov rdx, rdi
	mov r8, rsi
	add r8, 252
	mov eax, 32
23:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 1
24:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqa xmm3, xmm1
	psubd xmm3, xmm0
	paddd xmm3, xmm15
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
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
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm3
	add rdx, 16
	sub rcx, 1
	jne 24b
	add rdx, 16
	sub rax, 1
	jne 23b
	mov rdx, rdi
	mov r8, rsi
	add r8, 124
	mov eax, 16
25:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 2
26:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+32]
	movdqa xmm3, xmm1
	psubd xmm3, xmm0
	paddd xmm3, xmm15
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
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
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+32], xmm3
	add rdx, 16
	sub rcx, 1
	jne 26b
	add rdx, 32
	sub rax, 1
	jne 25b
	mov rdx, rdi
	mov r8, rsi
	add r8, 60
	mov eax, 8
27:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 4
28:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+64]
	movdqa xmm3, xmm1
	psubd xmm3, xmm0
	paddd xmm3, xmm15
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
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
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+64], xmm3
	add rdx, 16
	sub rcx, 1
	jne 28b
	add rdx, 64
	sub rax, 1
	jne 27b
	mov rdx, rdi
	mov r8, rsi
	add r8, 28
	mov eax, 4
29:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 8
210:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+128]
	movdqa xmm3, xmm1
	psubd xmm3, xmm0
	paddd xmm3, xmm15
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
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
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+128], xmm3
	add rdx, 16
	sub rcx, 1
	jne 210b
	add rdx, 128
	sub rax, 1
	jne 29b
	mov rdx, rdi
	mov r8, rsi
	add r8, 12
	mov eax, 2
211:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 16
212:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+256]
	movdqa xmm3, xmm1
	psubd xmm3, xmm0
	paddd xmm3, xmm15
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
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
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+256], xmm3
	add rdx, 16
	sub rcx, 1
	jne 212b
	add rdx, 256
	sub rax, 1
	jne 211b
	mov rdx, rdi
	mov r8, rsi
	add r8, 4
	mov eax, 1
213:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 32
214:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+512]
	movdqa xmm3, xmm1
	psubd xmm3, xmm0
	paddd xmm3, xmm15
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
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
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+512], xmm3
	add rdx, 16
	sub rcx, 1
	jne 214b
	add rdx, 512
	sub rax, 1
	jne 213b
	mov rdx, rdi
	mov eax, 16382
	movq xmm13, rax
	pshufd xmm13, xmm13, 0
	movdqa xmm12, xmm13
	mov ecx, 64
215:
	movdqu xmm3, XMMWORD PTR [rdx]
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
	psubd xmm3, xmm15
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm3
	add rdx, 16
	sub rcx, 1
	jne 215b
	lfence
	mov DWORD PTR [rsi+768], r11d
	ldmxcsr DWORD PTR [rsi+768]
	ret
	.p2align 6
