// The functions of `src/mldsa.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_ntt:
	stmxcsr DWORD PTR [rsi+768]
	mov r11d, DWORD PTR [rsi+768]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rsi+772], eax
	ldmxcsr DWORD PTR [rsi+772]
	lfence
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
	add r8, 4
	mov eax, 1
20:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, 4
	mov ecx, 32
21:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+512]
	pshufd xmm4, xmm1, 245
	pmuludq xmm1, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm1
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm1, xmm2
	psrlq xmm1, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm1, xmm4
	psubd xmm1, xmm15
	movdqa xmm2, xmm1
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm1, xmm2
	movdqa xmm3, xmm0
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	psubd xmm3, xmm1
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+512], xmm3
	add rdx, 16
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
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, 4
	mov ecx, 16
23:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+256]
	pshufd xmm4, xmm1, 245
	pmuludq xmm1, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm1
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm1, xmm2
	psrlq xmm1, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm1, xmm4
	psubd xmm1, xmm15
	movdqa xmm2, xmm1
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm1, xmm2
	movdqa xmm3, xmm0
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	psubd xmm3, xmm1
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+256], xmm3
	add rdx, 16
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
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, 4
	mov ecx, 8
25:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+128]
	pshufd xmm4, xmm1, 245
	pmuludq xmm1, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm1
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm1, xmm2
	psrlq xmm1, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm1, xmm4
	psubd xmm1, xmm15
	movdqa xmm2, xmm1
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm1, xmm2
	movdqa xmm3, xmm0
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	psubd xmm3, xmm1
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+128], xmm3
	add rdx, 16
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
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, 4
	mov ecx, 4
27:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+64]
	pshufd xmm4, xmm1, 245
	pmuludq xmm1, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm1
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm1, xmm2
	psrlq xmm1, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm1, xmm4
	psubd xmm1, xmm15
	movdqa xmm2, xmm1
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm1, xmm2
	movdqa xmm3, xmm0
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	psubd xmm3, xmm1
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+64], xmm3
	add rdx, 16
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
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, 4
	mov ecx, 2
29:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+32]
	pshufd xmm4, xmm1, 245
	pmuludq xmm1, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm1
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm1, xmm2
	psrlq xmm1, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm1, xmm4
	psubd xmm1, xmm15
	movdqa xmm2, xmm1
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm1, xmm2
	movdqa xmm3, xmm0
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	psubd xmm3, xmm1
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+32], xmm3
	add rdx, 16
	sub rcx, 1
	jne 29b
	add rdx, 32
	sub rax, 1
	jne 28b
	mov rdx, rdi
	mov r8, rsi
	add r8, 128
	mov eax, 32
210:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, 4
	mov ecx, 1
211:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	pshufd xmm4, xmm1, 245
	pmuludq xmm1, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm1
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm1, xmm2
	psrlq xmm1, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm1, xmm4
	psubd xmm1, xmm15
	movdqa xmm2, xmm1
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm1, xmm2
	movdqa xmm3, xmm0
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	psubd xmm3, xmm1
	movdqa xmm2, xmm3
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm3
	add rdx, 16
	sub rcx, 1
	jne 211b
	add rdx, 16
	sub rax, 1
	jne 210b
	mov rdx, rdi
	mov r8, rsi
	add r8, 256
	mov ecx, 32
212:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 80
	pshufd xmm12, xmm13, 245
	add r8, 8
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm1, xmm2
	pshufd xmm4, xmm1, 245
	pmuludq xmm1, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm1
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm1, xmm2
	psrlq xmm1, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm1, xmm4
	psubd xmm1, xmm15
	movdqa xmm2, xmm1
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm1, xmm2
	movdqa xmm3, xmm0
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	psubd xmm3, xmm1
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
	jne 212b
	mov rdx, rdi
	mov r8, rsi
	add r8, 512
	mov ecx, 32
213:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm2, XMMWORD PTR [rdx+16]
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 228
	pshufd xmm12, xmm13, 245
	add r8, 16
	pshufd xmm0, xmm0, 216
	pshufd xmm2, xmm2, 216
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	pshufd xmm4, xmm1, 245
	pmuludq xmm1, xmm13
	pmuludq xmm4, xmm12
	movdqa xmm2, xmm1
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm1, xmm2
	psrlq xmm1, 32
	movdqa xmm2, xmm4
	pmuludq xmm2, xmm14
	pmuludq xmm2, xmm15
	paddq xmm4, xmm2
	por xmm1, xmm4
	psubd xmm1, xmm15
	movdqa xmm2, xmm1
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm1, xmm2
	movdqa xmm3, xmm0
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	psubd xmm3, xmm1
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
	jne 213b
	lfence
	mov DWORD PTR [rsi+768], r11d
	ldmxcsr DWORD PTR [rsi+768]
	ret
	.p2align 6

vg_mldsa_inv_ntt:
	stmxcsr DWORD PTR [rsi+768]
	mov r11d, DWORD PTR [rsi+768]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rsi+772], eax
	ldmxcsr DWORD PTR [rsi+772]
	lfence
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
20:
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
	jne 20b
	mov rdx, rdi
	mov r8, rsi
	add r8, 504
	mov ecx, 32
21:
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
	jne 21b
	mov rdx, rdi
	mov r8, rsi
	add r8, 252
	mov eax, 32
22:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 1
23:
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
	jne 23b
	add rdx, 16
	sub rax, 1
	jne 22b
	mov rdx, rdi
	mov r8, rsi
	add r8, 124
	mov eax, 16
24:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 2
25:
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
	jne 25b
	add rdx, 32
	sub rax, 1
	jne 24b
	mov rdx, rdi
	mov r8, rsi
	add r8, 60
	mov eax, 8
26:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 4
27:
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
	jne 27b
	add rdx, 64
	sub rax, 1
	jne 26b
	mov rdx, rdi
	mov r8, rsi
	add r8, 28
	mov eax, 4
28:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 8
29:
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
	jne 29b
	add rdx, 128
	sub rax, 1
	jne 28b
	mov rdx, rdi
	mov r8, rsi
	add r8, 12
	mov eax, 2
210:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 16
211:
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
	jne 211b
	add rdx, 256
	sub rax, 1
	jne 210b
	mov rdx, rdi
	mov r8, rsi
	add r8, 4
	mov eax, 1
212:
	movdqu xmm13, XMMWORD PTR [r8]
	pshufd xmm13, xmm13, 0
	pshufd xmm12, xmm13, 245
	add r8, -4
	mov ecx, 32
213:
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
	jne 213b
	add rdx, 512
	sub rax, 1
	jne 212b
	mov rdx, rdi
	mov eax, 16382
	movq xmm13, rax
	pshufd xmm13, xmm13, 0
	movdqa xmm12, xmm13
	mov ecx, 64
214:
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
	jne 214b
	lfence
	mov DWORD PTR [rsi+768], r11d
	ldmxcsr DWORD PTR [rsi+768]
	ret
	.p2align 6

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

vg_mldsa_multiply_add_ntt:
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
	paddd xmm3, xmm5
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
	paddd xmm3, xmm5
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

vg_mldsa_add:
	mov eax, 8380417
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov ecx, 64
20:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu xmm1, XMMWORD PTR [rsi]
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rsi, 16
	sub rcx, 1
	jne 20b
	ret
	.p2align 6

vg_mldsa_sub:
	mov eax, 8380417
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov ecx, 64
20:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu xmm1, XMMWORD PTR [rsi]
	psubd xmm0, xmm1
	movdqa xmm2, xmm0
	psrad xmm2, 31
	pand xmm2, xmm15
	paddd xmm0, xmm2
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rsi, 16
	sub rcx, 1
	jne 20b
	ret
	.p2align 6

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

vg_mldsa_montgomery_inv_ntt_avx2:
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
	mov eax, 1072693376
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov rdx, rdi
	mov r8, rsi
	add r8, 992
	mov ecx, 16
20:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm2, YMMWORD PTR [rdx+32]
	vmovdqu ymm13, YMMWORD PTR [r8]
	vpermq ymm13, ymm13, 39
	vpshufd ymm13, ymm13, 177
	vpshufd ymm12, ymm13, 245
	add r8, -32
	vpshufd ymm0, ymm0, 216
	vpshufd ymm2, ymm2, 216
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm2
	vpunpckhqdq ymm1, ymm1, ymm2
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqa ymm1, ymm0
	vpunpckldq ymm0, ymm0, ymm3
	vpunpckhdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 20b
	mov rdx, rdi
	mov r8, rsi
	add r8, 496
	mov ecx, 16
21:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 10
	vpshufd ymm13, ymm13, 95
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, -16
	vmovdqa ymm2, ymm0
	vpunpcklqdq ymm0, ymm0, ymm1
	vpunpckhqdq ymm2, ymm2, ymm1
	vmovdqa ymm1, ymm2
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm3
	vpunpckhqdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 21b
	mov rdx, rdi
	mov r8, rsi
	add r8, 248
	mov ecx, 16
22:
	vmovdqu ymm4, YMMWORD PTR [rdx]
	vmovdqu ymm5, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 0
	vpshufd ymm13, ymm13, 85
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, -8
	vperm2i128 ymm0, ymm4, ymm5, 32
	vperm2i128 ymm1, ymm4, ymm5, 49
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vperm2i128 ymm4, ymm0, ymm3, 32
	vperm2i128 ymm5, ymm0, ymm3, 49
	vmovdqu YMMWORD PTR [rdx], ymm4
	vmovdqu YMMWORD PTR [rdx+32], ymm5
	add rdx, 64
	sub rcx, 1
	jne 22b
	mov rdx, rdi
	mov r8, rsi
	add r8, 124
	mov eax, 16
23:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 1
24:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm3
	add rdx, 32
	sub rcx, 1
	jne 24b
	add rdx, 32
	sub rax, 1
	jne 23b
	mov rdx, rdi
	mov r8, rsi
	add r8, 60
	mov eax, 8
25:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 2
26:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+64]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+64], ymm3
	add rdx, 32
	sub rcx, 1
	jne 26b
	add rdx, 64
	sub rax, 1
	jne 25b
	mov rdx, rdi
	mov r8, rsi
	add r8, 28
	mov eax, 4
27:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 4
28:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+128]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	add rdx, 32
	sub rcx, 1
	jne 28b
	add rdx, 128
	sub rax, 1
	jne 27b
	mov rdx, rdi
	mov eax, 7861508
	vmovq xmm7, rax
	vpbroadcastd ymm7, xmm7
	mov eax, 5771523
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 4404704
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 41978
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov ecx, 8
29:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+256]
	vmovdqu ymm5, YMMWORD PTR [rdx+512]
	vmovdqu ymm6, YMMWORD PTR [rdx+768]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm7
	vpmuludq ymm4, ymm4, ymm7
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm1, ymm6, ymm5
	vpaddd ymm1, ymm1, ymm11
	vpaddd ymm5, ymm5, ymm6
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm8
	vpmuludq ymm4, ymm4, ymm8
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vpsubd ymm6, ymm5, ymm0
	vpaddd ymm6, ymm6, ymm11
	vpaddd ymm0, ymm0, ymm5
	vpshufd ymm4, ymm6, 245
	vpmuludq ymm6, ymm6, ymm9
	vpmuludq ymm4, ymm4, ymm9
	vpmuludq ymm2, ymm6, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm6, ymm6, ymm2
	vpsrlq ymm6, ymm6, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm6, ymm6, ymm4
	vpsubd ymm5, ymm1, ymm3
	vpaddd ymm5, ymm5, ymm11
	vpaddd ymm3, ymm3, ymm1
	vpshufd ymm4, ymm5, 245
	vpmuludq ymm5, ymm5, ymm9
	vpmuludq ymm4, ymm4, ymm9
	vpmuludq ymm2, ymm5, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm5, ymm5, ymm2
	vpsrlq ymm5, ymm5, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm5, ymm5, ymm4
	vpshufd ymm4, ymm0, 245
	vpmuludq ymm0, ymm0, ymm10
	vpmuludq ymm4, ymm4, ymm10
	vpmuludq ymm2, ymm0, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm0, ymm0, ymm2
	vpsrlq ymm0, ymm0, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm0, ymm0, ymm4
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm2, ymm0, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm0, ymm0, ymm2
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm10
	vpmuludq ymm4, ymm4, ymm10
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	vpsubd ymm6, ymm6, ymm15
	vpsrad ymm2, ymm6, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm6, ymm6, ymm2
	vpsubd ymm5, ymm5, ymm15
	vpsrad ymm2, ymm5, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm5, ymm5, ymm2
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+256], ymm3
	vmovdqu YMMWORD PTR [rdx+512], ymm6
	vmovdqu YMMWORD PTR [rdx+768], ymm5
	add rdx, 32
	sub rcx, 1
	jne 29b
	vzeroupper
	lfence
	mov DWORD PTR [rsi+768], r11d
	ldmxcsr DWORD PTR [rsi+768]
	ret
	.p2align 6

vg_mldsa_montgomery_multiply_ntt_avx2:
	mov r8, rdi
	vmovdqu ymm6, YMMWORD PTR [rdi+992]
	stmxcsr DWORD PTR [r8+1016]
	mov r11d, DWORD PTR [r8+1016]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [r8+1020], eax
	ldmxcsr DWORD PTR [r8+1020]
	lfence
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -58728449
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov eax, 2365951
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 31
20:
	vmovdqu ymm3, YMMWORD PTR [rsi]
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vmovdqu ymm5, YMMWORD PTR [rdi]
	vpshufd ymm12, ymm13, 245
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	vmovdqu YMMWORD PTR [rdi], ymm3
	add rdi, 32
	add rsi, 32
	add rdx, 32
	sub rcx, 1
	jne 20b
	vmovdqu ymm3, YMMWORD PTR [rsi]
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vmovdqa ymm5, ymm6
	vpshufd ymm12, ymm13, 245
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	lfence
	mov DWORD PTR [r8+1016], r11d
	ldmxcsr DWORD PTR [r8+1016]
	vmovdqu YMMWORD PTR [rdi], ymm3
	vzeroupper
	ret
	.p2align 6

vg_mldsa_montgomery_multiply_add_ntt_avx2:
	mov r8, rdi
	vmovdqu ymm6, YMMWORD PTR [rdi+992]
	stmxcsr DWORD PTR [r8+1016]
	mov r11d, DWORD PTR [r8+1016]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [r8+1020], eax
	ldmxcsr DWORD PTR [r8+1020]
	lfence
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -58728449
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov eax, 2365951
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 31
20:
	vmovdqu ymm3, YMMWORD PTR [rsi]
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vmovdqu ymm5, YMMWORD PTR [rdi]
	vpshufd ymm12, ymm13, 245
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	vpaddd ymm3, ymm3, ymm5
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	vmovdqu YMMWORD PTR [rdi], ymm3
	add rdi, 32
	add rsi, 32
	add rdx, 32
	sub rcx, 1
	jne 20b
	vmovdqu ymm3, YMMWORD PTR [rsi]
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vmovdqa ymm5, ymm6
	vpshufd ymm12, ymm13, 245
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	vpaddd ymm3, ymm3, ymm5
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	lfence
	mov DWORD PTR [r8+1016], r11d
	ldmxcsr DWORD PTR [r8+1016]
	vmovdqu YMMWORD PTR [rdi], ymm3
	vzeroupper
	ret
	.p2align 6

vg_mldsa_add_avx2:
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
20:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm2, ymm0, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm0, ymm0, ymm2
	vmovdqu YMMWORD PTR [rdi], ymm0
	add rdi, 32
	add rsi, 32
	sub rcx, 1
	jne 20b
	vzeroupper
	ret
	.p2align 6

vg_mldsa_sub_avx2:
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
20:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vpsubd ymm0, ymm0, ymm1
	vpsrad ymm2, ymm0, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm0, ymm0, ymm2
	vmovdqu YMMWORD PTR [rdi], ymm0
	add rdi, 32
	add rsi, 32
	sub rcx, 1
	jne 20b
	vzeroupper
	ret
	.p2align 6

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

vg_mldsa_dot_inverse5:
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
	movdqu xmm0, XMMWORD PTR [r10+4096]
	movdqu xmm1, XMMWORD PTR [rdx+4096]
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

vg_mldsa_dot_inverse7:
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
	movdqu xmm0, XMMWORD PTR [r10+4096]
	movdqu xmm1, XMMWORD PTR [rdx+4096]
	movdqa xmm2, xmm0
	psrlq xmm2, 32
	movdqa xmm3, xmm1
	psrlq xmm3, 32
	pmuludq xmm2, xmm3
	pmuludq xmm0, xmm1
	paddq xmm5, xmm0
	paddq xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [r10+5120]
	movdqu xmm1, XMMWORD PTR [rdx+5120]
	movdqa xmm2, xmm0
	psrlq xmm2, 32
	movdqa xmm3, xmm1
	psrlq xmm3, 32
	pmuludq xmm2, xmm3
	pmuludq xmm0, xmm1
	paddq xmm5, xmm0
	paddq xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [r10+6144]
	movdqu xmm1, XMMWORD PTR [rdx+6144]
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

vg_mldsa_dot_inverse4_avx2:
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
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -58728449
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov r8, rdi
	mov ecx, 32
20:
	vpxor ymm5, ymm5, ymm5
	vpxor ymm6, ymm6, ymm6
	vmovdqu ymm0, YMMWORD PTR [r10]
	vmovdqu ymm1, YMMWORD PTR [rdx]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+1024]
	vmovdqu ymm1, YMMWORD PTR [rdx+1024]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+2048]
	vmovdqu ymm1, YMMWORD PTR [rdx+2048]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+3072]
	vmovdqu ymm1, YMMWORD PTR [rdx+3072]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vpmuludq ymm2, ymm5, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm5, ymm5, ymm2
	vpsrlq ymm5, ymm5, 32
	vpmuludq ymm2, ymm6, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm6, ymm6, ymm2
	vpor ymm5, ymm5, ymm6
	vpsubd ymm5, ymm5, ymm15
	vpsrad ymm2, ymm5, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm5, ymm5, ymm2
	vmovdqu YMMWORD PTR [r8], ymm5
	add r8, 32
	add r10, 32
	add rdx, 32
	sub rcx, 1
	jne 20b
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
	mov eax, 1072693376
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov rdx, rdi
	mov r8, rsi
	add r8, 992
	mov ecx, 16
21:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm2, YMMWORD PTR [rdx+32]
	vmovdqu ymm13, YMMWORD PTR [r8]
	vpermq ymm13, ymm13, 39
	vpshufd ymm13, ymm13, 177
	vpshufd ymm12, ymm13, 245
	add r8, -32
	vpshufd ymm0, ymm0, 216
	vpshufd ymm2, ymm2, 216
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm2
	vpunpckhqdq ymm1, ymm1, ymm2
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqa ymm1, ymm0
	vpunpckldq ymm0, ymm0, ymm3
	vpunpckhdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 21b
	mov rdx, rdi
	mov r8, rsi
	add r8, 496
	mov ecx, 16
22:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 10
	vpshufd ymm13, ymm13, 95
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, -16
	vmovdqa ymm2, ymm0
	vpunpcklqdq ymm0, ymm0, ymm1
	vpunpckhqdq ymm2, ymm2, ymm1
	vmovdqa ymm1, ymm2
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm3
	vpunpckhqdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 22b
	mov rdx, rdi
	mov r8, rsi
	add r8, 248
	mov ecx, 16
23:
	vmovdqu ymm4, YMMWORD PTR [rdx]
	vmovdqu ymm5, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 0
	vpshufd ymm13, ymm13, 85
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, -8
	vperm2i128 ymm0, ymm4, ymm5, 32
	vperm2i128 ymm1, ymm4, ymm5, 49
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vperm2i128 ymm4, ymm0, ymm3, 32
	vperm2i128 ymm5, ymm0, ymm3, 49
	vmovdqu YMMWORD PTR [rdx], ymm4
	vmovdqu YMMWORD PTR [rdx+32], ymm5
	add rdx, 64
	sub rcx, 1
	jne 23b
	mov rdx, rdi
	mov r8, rsi
	add r8, 124
	mov eax, 16
24:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 1
25:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm3
	add rdx, 32
	sub rcx, 1
	jne 25b
	add rdx, 32
	sub rax, 1
	jne 24b
	mov rdx, rdi
	mov r8, rsi
	add r8, 60
	mov eax, 8
26:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 2
27:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+64]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
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
	add r8, 28
	mov eax, 4
28:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 4
29:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+128]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	add rdx, 32
	sub rcx, 1
	jne 29b
	add rdx, 128
	sub rax, 1
	jne 28b
	mov rdx, rdi
	mov eax, 7861508
	vmovq xmm7, rax
	vpbroadcastd ymm7, xmm7
	mov eax, 5771523
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 4404704
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 41978
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov ecx, 8
210:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+256]
	vmovdqu ymm5, YMMWORD PTR [rdx+512]
	vmovdqu ymm6, YMMWORD PTR [rdx+768]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm7
	vpmuludq ymm4, ymm4, ymm7
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm1, ymm6, ymm5
	vpaddd ymm1, ymm1, ymm11
	vpaddd ymm5, ymm5, ymm6
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm8
	vpmuludq ymm4, ymm4, ymm8
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vpsubd ymm6, ymm5, ymm0
	vpaddd ymm6, ymm6, ymm11
	vpaddd ymm0, ymm0, ymm5
	vpshufd ymm4, ymm6, 245
	vpmuludq ymm6, ymm6, ymm9
	vpmuludq ymm4, ymm4, ymm9
	vpmuludq ymm2, ymm6, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm6, ymm6, ymm2
	vpsrlq ymm6, ymm6, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm6, ymm6, ymm4
	vpsubd ymm5, ymm1, ymm3
	vpaddd ymm5, ymm5, ymm11
	vpaddd ymm3, ymm3, ymm1
	vpshufd ymm4, ymm5, 245
	vpmuludq ymm5, ymm5, ymm9
	vpmuludq ymm4, ymm4, ymm9
	vpmuludq ymm2, ymm5, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm5, ymm5, ymm2
	vpsrlq ymm5, ymm5, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm5, ymm5, ymm4
	vpshufd ymm4, ymm0, 245
	vpmuludq ymm0, ymm0, ymm10
	vpmuludq ymm4, ymm4, ymm10
	vpmuludq ymm2, ymm0, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm0, ymm0, ymm2
	vpsrlq ymm0, ymm0, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm0, ymm0, ymm4
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm2, ymm0, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm0, ymm0, ymm2
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm10
	vpmuludq ymm4, ymm4, ymm10
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	vpsubd ymm6, ymm6, ymm15
	vpsrad ymm2, ymm6, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm6, ymm6, ymm2
	vpsubd ymm5, ymm5, ymm15
	vpsrad ymm2, ymm5, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm5, ymm5, ymm2
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+256], ymm3
	vmovdqu YMMWORD PTR [rdx+512], ymm6
	vmovdqu YMMWORD PTR [rdx+768], ymm5
	add rdx, 32
	sub rcx, 1
	jne 210b
	vzeroupper
	lfence
	mov DWORD PTR [rsi+768], r11d
	ldmxcsr DWORD PTR [rsi+768]
	ret
	.p2align 6

vg_mldsa_dot_inverse5_avx2:
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
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -58728449
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov r8, rdi
	mov ecx, 32
20:
	vpxor ymm5, ymm5, ymm5
	vpxor ymm6, ymm6, ymm6
	vmovdqu ymm0, YMMWORD PTR [r10]
	vmovdqu ymm1, YMMWORD PTR [rdx]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+1024]
	vmovdqu ymm1, YMMWORD PTR [rdx+1024]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+2048]
	vmovdqu ymm1, YMMWORD PTR [rdx+2048]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+3072]
	vmovdqu ymm1, YMMWORD PTR [rdx+3072]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+4096]
	vmovdqu ymm1, YMMWORD PTR [rdx+4096]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vpmuludq ymm2, ymm5, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm5, ymm5, ymm2
	vpsrlq ymm5, ymm5, 32
	vpmuludq ymm2, ymm6, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm6, ymm6, ymm2
	vpor ymm5, ymm5, ymm6
	vpsubd ymm5, ymm5, ymm15
	vpsrad ymm2, ymm5, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm5, ymm5, ymm2
	vmovdqu YMMWORD PTR [r8], ymm5
	add r8, 32
	add r10, 32
	add rdx, 32
	sub rcx, 1
	jne 20b
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
	mov eax, 1072693376
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov rdx, rdi
	mov r8, rsi
	add r8, 992
	mov ecx, 16
21:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm2, YMMWORD PTR [rdx+32]
	vmovdqu ymm13, YMMWORD PTR [r8]
	vpermq ymm13, ymm13, 39
	vpshufd ymm13, ymm13, 177
	vpshufd ymm12, ymm13, 245
	add r8, -32
	vpshufd ymm0, ymm0, 216
	vpshufd ymm2, ymm2, 216
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm2
	vpunpckhqdq ymm1, ymm1, ymm2
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqa ymm1, ymm0
	vpunpckldq ymm0, ymm0, ymm3
	vpunpckhdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 21b
	mov rdx, rdi
	mov r8, rsi
	add r8, 496
	mov ecx, 16
22:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 10
	vpshufd ymm13, ymm13, 95
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, -16
	vmovdqa ymm2, ymm0
	vpunpcklqdq ymm0, ymm0, ymm1
	vpunpckhqdq ymm2, ymm2, ymm1
	vmovdqa ymm1, ymm2
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm3
	vpunpckhqdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 22b
	mov rdx, rdi
	mov r8, rsi
	add r8, 248
	mov ecx, 16
23:
	vmovdqu ymm4, YMMWORD PTR [rdx]
	vmovdqu ymm5, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 0
	vpshufd ymm13, ymm13, 85
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, -8
	vperm2i128 ymm0, ymm4, ymm5, 32
	vperm2i128 ymm1, ymm4, ymm5, 49
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vperm2i128 ymm4, ymm0, ymm3, 32
	vperm2i128 ymm5, ymm0, ymm3, 49
	vmovdqu YMMWORD PTR [rdx], ymm4
	vmovdqu YMMWORD PTR [rdx+32], ymm5
	add rdx, 64
	sub rcx, 1
	jne 23b
	mov rdx, rdi
	mov r8, rsi
	add r8, 124
	mov eax, 16
24:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 1
25:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm3
	add rdx, 32
	sub rcx, 1
	jne 25b
	add rdx, 32
	sub rax, 1
	jne 24b
	mov rdx, rdi
	mov r8, rsi
	add r8, 60
	mov eax, 8
26:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 2
27:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+64]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
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
	add r8, 28
	mov eax, 4
28:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 4
29:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+128]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	add rdx, 32
	sub rcx, 1
	jne 29b
	add rdx, 128
	sub rax, 1
	jne 28b
	mov rdx, rdi
	mov eax, 7861508
	vmovq xmm7, rax
	vpbroadcastd ymm7, xmm7
	mov eax, 5771523
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 4404704
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 41978
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov ecx, 8
210:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+256]
	vmovdqu ymm5, YMMWORD PTR [rdx+512]
	vmovdqu ymm6, YMMWORD PTR [rdx+768]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm7
	vpmuludq ymm4, ymm4, ymm7
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm1, ymm6, ymm5
	vpaddd ymm1, ymm1, ymm11
	vpaddd ymm5, ymm5, ymm6
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm8
	vpmuludq ymm4, ymm4, ymm8
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vpsubd ymm6, ymm5, ymm0
	vpaddd ymm6, ymm6, ymm11
	vpaddd ymm0, ymm0, ymm5
	vpshufd ymm4, ymm6, 245
	vpmuludq ymm6, ymm6, ymm9
	vpmuludq ymm4, ymm4, ymm9
	vpmuludq ymm2, ymm6, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm6, ymm6, ymm2
	vpsrlq ymm6, ymm6, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm6, ymm6, ymm4
	vpsubd ymm5, ymm1, ymm3
	vpaddd ymm5, ymm5, ymm11
	vpaddd ymm3, ymm3, ymm1
	vpshufd ymm4, ymm5, 245
	vpmuludq ymm5, ymm5, ymm9
	vpmuludq ymm4, ymm4, ymm9
	vpmuludq ymm2, ymm5, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm5, ymm5, ymm2
	vpsrlq ymm5, ymm5, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm5, ymm5, ymm4
	vpshufd ymm4, ymm0, 245
	vpmuludq ymm0, ymm0, ymm10
	vpmuludq ymm4, ymm4, ymm10
	vpmuludq ymm2, ymm0, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm0, ymm0, ymm2
	vpsrlq ymm0, ymm0, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm0, ymm0, ymm4
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm2, ymm0, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm0, ymm0, ymm2
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm10
	vpmuludq ymm4, ymm4, ymm10
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	vpsubd ymm6, ymm6, ymm15
	vpsrad ymm2, ymm6, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm6, ymm6, ymm2
	vpsubd ymm5, ymm5, ymm15
	vpsrad ymm2, ymm5, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm5, ymm5, ymm2
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+256], ymm3
	vmovdqu YMMWORD PTR [rdx+512], ymm6
	vmovdqu YMMWORD PTR [rdx+768], ymm5
	add rdx, 32
	sub rcx, 1
	jne 210b
	vzeroupper
	lfence
	mov DWORD PTR [rsi+768], r11d
	ldmxcsr DWORD PTR [rsi+768]
	ret
	.p2align 6

vg_mldsa_dot_inverse7_avx2:
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
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -58728449
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov r8, rdi
	mov ecx, 32
20:
	vpxor ymm5, ymm5, ymm5
	vpxor ymm6, ymm6, ymm6
	vmovdqu ymm0, YMMWORD PTR [r10]
	vmovdqu ymm1, YMMWORD PTR [rdx]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+1024]
	vmovdqu ymm1, YMMWORD PTR [rdx+1024]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+2048]
	vmovdqu ymm1, YMMWORD PTR [rdx+2048]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+3072]
	vmovdqu ymm1, YMMWORD PTR [rdx+3072]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+4096]
	vmovdqu ymm1, YMMWORD PTR [rdx+4096]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+5120]
	vmovdqu ymm1, YMMWORD PTR [rdx+5120]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vmovdqu ymm0, YMMWORD PTR [r10+6144]
	vmovdqu ymm1, YMMWORD PTR [rdx+6144]
	vpsrlq ymm2, ymm0, 32
	vpsrlq ymm3, ymm1, 32
	vpmuludq ymm2, ymm2, ymm3
	vpmuludq ymm0, ymm0, ymm1
	vpaddq ymm5, ymm5, ymm0
	vpaddq ymm6, ymm6, ymm2
	vpmuludq ymm2, ymm5, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm5, ymm5, ymm2
	vpsrlq ymm5, ymm5, 32
	vpmuludq ymm2, ymm6, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm6, ymm6, ymm2
	vpor ymm5, ymm5, ymm6
	vpsubd ymm5, ymm5, ymm15
	vpsrad ymm2, ymm5, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm5, ymm5, ymm2
	vmovdqu YMMWORD PTR [r8], ymm5
	add r8, 32
	add r10, 32
	add rdx, 32
	sub rcx, 1
	jne 20b
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
	mov eax, 1072693376
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov rdx, rdi
	mov r8, rsi
	add r8, 992
	mov ecx, 16
21:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm2, YMMWORD PTR [rdx+32]
	vmovdqu ymm13, YMMWORD PTR [r8]
	vpermq ymm13, ymm13, 39
	vpshufd ymm13, ymm13, 177
	vpshufd ymm12, ymm13, 245
	add r8, -32
	vpshufd ymm0, ymm0, 216
	vpshufd ymm2, ymm2, 216
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm2
	vpunpckhqdq ymm1, ymm1, ymm2
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqa ymm1, ymm0
	vpunpckldq ymm0, ymm0, ymm3
	vpunpckhdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 21b
	mov rdx, rdi
	mov r8, rsi
	add r8, 496
	mov ecx, 16
22:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 10
	vpshufd ymm13, ymm13, 95
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, -16
	vmovdqa ymm2, ymm0
	vpunpcklqdq ymm0, ymm0, ymm1
	vpunpckhqdq ymm2, ymm2, ymm1
	vmovdqa ymm1, ymm2
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqa ymm1, ymm0
	vpunpcklqdq ymm0, ymm0, ymm3
	vpunpckhqdq ymm1, ymm1, ymm3
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	add rdx, 64
	sub rcx, 1
	jne 22b
	mov rdx, rdi
	mov r8, rsi
	add r8, 248
	mov ecx, 16
23:
	vmovdqu ymm4, YMMWORD PTR [rdx]
	vmovdqu ymm5, YMMWORD PTR [rdx+32]
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm2, ymm13, 0
	vpshufd ymm13, ymm13, 85
	vpblendd ymm13, ymm13, ymm2, 240
	vpshufd ymm12, ymm13, 245
	add r8, -8
	vperm2i128 ymm0, ymm4, ymm5, 32
	vperm2i128 ymm1, ymm4, ymm5, 49
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vperm2i128 ymm4, ymm0, ymm3, 32
	vperm2i128 ymm5, ymm0, ymm3, 49
	vmovdqu YMMWORD PTR [rdx], ymm4
	vmovdqu YMMWORD PTR [rdx+32], ymm5
	add rdx, 64
	sub rcx, 1
	jne 23b
	mov rdx, rdi
	mov r8, rsi
	add r8, 124
	mov eax, 16
24:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 1
25:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm3
	add rdx, 32
	sub rcx, 1
	jne 25b
	add rdx, 32
	sub rax, 1
	jne 24b
	mov rdx, rdi
	mov r8, rsi
	add r8, 60
	mov eax, 8
26:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 2
27:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+64]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
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
	add r8, 28
	mov eax, 4
28:
	vbroadcasti128 ymm13, XMMWORD PTR [r8]
	vpshufd ymm13, ymm13, 0
	vpshufd ymm12, ymm13, 245
	add r8, -4
	mov ecx, 4
29:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+128]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	add rdx, 32
	sub rcx, 1
	jne 29b
	add rdx, 128
	sub rax, 1
	jne 28b
	mov rdx, rdi
	mov eax, 7861508
	vmovq xmm7, rax
	vpbroadcastd ymm7, xmm7
	mov eax, 5771523
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 4404704
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 41978
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov ecx, 8
210:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+256]
	vmovdqu ymm5, YMMWORD PTR [rdx+512]
	vmovdqu ymm6, YMMWORD PTR [rdx+768]
	vpsubd ymm3, ymm1, ymm0
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm7
	vpmuludq ymm4, ymm4, ymm7
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm1, ymm6, ymm5
	vpaddd ymm1, ymm1, ymm11
	vpaddd ymm5, ymm5, ymm6
	vpshufd ymm4, ymm1, 245
	vpmuludq ymm1, ymm1, ymm8
	vpmuludq ymm4, ymm4, ymm8
	vpmuludq ymm2, ymm1, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm1, ymm1, ymm2
	vpsrlq ymm1, ymm1, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm1, ymm1, ymm4
	vpsubd ymm6, ymm5, ymm0
	vpaddd ymm6, ymm6, ymm11
	vpaddd ymm0, ymm0, ymm5
	vpshufd ymm4, ymm6, 245
	vpmuludq ymm6, ymm6, ymm9
	vpmuludq ymm4, ymm4, ymm9
	vpmuludq ymm2, ymm6, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm6, ymm6, ymm2
	vpsrlq ymm6, ymm6, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm6, ymm6, ymm4
	vpsubd ymm5, ymm1, ymm3
	vpaddd ymm5, ymm5, ymm11
	vpaddd ymm3, ymm3, ymm1
	vpshufd ymm4, ymm5, 245
	vpmuludq ymm5, ymm5, ymm9
	vpmuludq ymm4, ymm4, ymm9
	vpmuludq ymm2, ymm5, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm5, ymm5, ymm2
	vpsrlq ymm5, ymm5, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm5, ymm5, ymm4
	vpshufd ymm4, ymm0, 245
	vpmuludq ymm0, ymm0, ymm10
	vpmuludq ymm4, ymm4, ymm10
	vpmuludq ymm2, ymm0, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm0, ymm0, ymm2
	vpsrlq ymm0, ymm0, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm0, ymm0, ymm4
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm2, ymm0, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm0, ymm0, ymm2
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm10
	vpmuludq ymm4, ymm4, ymm10
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	vpsubd ymm6, ymm6, ymm15
	vpsrad ymm2, ymm6, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm6, ymm6, ymm2
	vpsubd ymm5, ymm5, ymm15
	vpsrad ymm2, ymm5, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm5, ymm5, ymm2
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+256], ymm3
	vmovdqu YMMWORD PTR [rdx+512], ymm6
	vmovdqu YMMWORD PTR [rdx+768], ymm5
	add rdx, 32
	sub rcx, 1
	jne 210b
	vzeroupper
	lfence
	mov DWORD PTR [rsi+768], r11d
	ldmxcsr DWORD PTR [rsi+768]
	ret
	.p2align 6

vg_mldsa_simple_bit_pack:
	mov esi, esi
	mov r8, rdx
	cmp esi, 15
	je 20f
	cmp esi, 43
	je 22f
	mov ecx, 64
24:
	mov r10d, 0
	mov eax, DWORD PTR [rdi]
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+4]
	ror rax, 62
	add r10, rax
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+8]
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+12]
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8+3], r10b
	shr r10, 8
	mov BYTE PTR [r8+4], r10b
	shr r10, 8
	add rdi, 16
	add r8, 5
	sub rcx, 1
	jne 24b
	jmp 23f
22:
	mov ecx, 64
25:
	mov r10d, 0
	mov eax, DWORD PTR [rdi]
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+8]
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+12]
	ror rax, 62
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	add rdi, 16
	add r8, 3
	sub rcx, 1
	jne 25b
23:
	jmp 21f
20:
	mov ecx, 128
26:
	mov r10d, 0
	mov eax, DWORD PTR [rdi]
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	add rdi, 8
	add r8, 1
	sub rcx, 1
	jne 26b
21:
	ret
	.p2align 6

vg_mldsa_bit_pack:
	mov edx, edx
	mov r8, rcx
	cmp edx, 2
	je 20f
	cmp edx, 4
	je 22f
	cmp edx, 4096
	je 24f
	cmp edx, 131072
	je 26f
	mov ecx, 128
28:
	mov r10d, 0
	mov eax, 524288
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, 524288
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	mov BYTE PTR [r8+3], r10b
	shr r10, 8
	mov BYTE PTR [r8+4], r10b
	shr r10, 8
	add rdi, 8
	add r8, 5
	sub rcx, 1
	jne 28b
	jmp 27f
26:
	mov ecx, 64
29:
	mov r10d, 0
	mov eax, 131072
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, 131072
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 62
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	mov BYTE PTR [r8+3], r10b
	shr r10, 8
	mov eax, 131072
	sub eax, DWORD PTR [rdi+8]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+4], r10b
	shr r10, 8
	mov BYTE PTR [r8+5], r10b
	shr r10, 8
	mov eax, 131072
	sub eax, DWORD PTR [rdi+12]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8+6], r10b
	shr r10, 8
	mov BYTE PTR [r8+7], r10b
	shr r10, 8
	mov BYTE PTR [r8+8], r10b
	shr r10, 8
	add rdi, 16
	add r8, 9
	sub rcx, 1
	jne 29b
27:
	jmp 25f
24:
	mov ecx, 32
210:
	mov r10d, 0
	mov eax, 4096
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 59
	add r10, rax
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+8]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 62
	add r10, rax
	mov BYTE PTR [r8+3], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+12]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 57
	add r10, rax
	mov BYTE PTR [r8+4], r10b
	shr r10, 8
	mov BYTE PTR [r8+5], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+16]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+6], r10b
	shr r10, 8
	mov BYTE PTR [r8+7], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+20]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 63
	add r10, rax
	mov BYTE PTR [r8+8], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+24]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8+9], r10b
	shr r10, 8
	mov BYTE PTR [r8+10], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+28]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 61
	add r10, rax
	mov BYTE PTR [r8+11], r10b
	shr r10, 8
	mov BYTE PTR [r8+12], r10b
	shr r10, 8
	add rdi, 32
	add r8, 13
	sub rcx, 1
	jne 210b
25:
	jmp 23f
22:
	mov ecx, 128
211:
	mov r10d, 0
	mov eax, 4
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov eax, 4
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	add rdi, 8
	add r8, 1
	sub rcx, 1
	jne 211b
23:
	jmp 21f
20:
	mov ecx, 32
212:
	mov r10d, 0
	mov eax, 2
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 61
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+8]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov eax, 2
	sub eax, DWORD PTR [rdi+12]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 63
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+16]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+20]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 57
	add r10, rax
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, 2
	sub eax, DWORD PTR [rdi+24]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 62
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+28]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 59
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	add rdi, 32
	add r8, 3
	sub rcx, 1
	jne 212b
21:
	ret
	.p2align 6

vg_mldsa_bit_unpack:
	mov ecx, ecx
	mov rsi, r8
	cmp ecx, 2
	je 20f
	cmp ecx, 4
	je 22f
	cmp ecx, 4096
	je 24f
	cmp ecx, 131072
	je 26f
	mov ecx, 128
28:
	mov eax, DWORD PTR [rdi]
	and eax, 1048575
	mov r11d, 524288
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	mov eax, DWORD PTR [rdi+1]
	shr eax, 12
	and eax, 1048575
	mov r11d, 524288
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	add rdi, 5
	add rsi, 8
	sub rcx, 1
	jne 28b
	jmp 27f
26:
	mov ecx, 64
29:
	mov eax, DWORD PTR [rdi]
	and eax, 262143
	mov r11d, 131072
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	mov eax, DWORD PTR [rdi+2]
	shr eax, 2
	and eax, 262143
	mov r11d, 131072
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	mov eax, DWORD PTR [rdi+4]
	shr eax, 4
	and eax, 262143
	mov r11d, 131072
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+8], r11d
	mov eax, DWORD PTR [rdi+5]
	shr eax, 14
	and eax, 262143
	mov r11d, 131072
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+12], r11d
	add rdi, 9
	add rsi, 16
	sub rcx, 1
	jne 29b
27:
	jmp 25f
24:
	mov ecx, 32
210:
	mov eax, DWORD PTR [rdi]
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	mov eax, DWORD PTR [rdi+1]
	shr eax, 5
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	mov eax, DWORD PTR [rdi+3]
	shr eax, 2
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+8], r11d
	mov eax, DWORD PTR [rdi+4]
	shr eax, 7
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+12], r11d
	mov eax, DWORD PTR [rdi+6]
	shr eax, 4
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+16], r11d
	mov eax, DWORD PTR [rdi+8]
	shr eax, 1
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+20], r11d
	mov eax, DWORD PTR [rdi+9]
	shr eax, 6
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+24], r11d
	mov eax, DWORD PTR [rdi+9]
	shr eax, 19
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+28], r11d
	add rdi, 13
	add rsi, 32
	sub rcx, 1
	jne 210b
25:
	jmp 23f
22:
	mov ecx, 64
211:
	movzx eax, WORD PTR [rdi]
	and eax, 15
	mov r11d, 4
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 4
	and eax, 15
	mov r11d, 4
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 8
	and eax, 15
	mov r11d, 4
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+8], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 12
	and eax, 15
	mov r11d, 4
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+12], r11d
	add rdi, 2
	add rsi, 16
	sub rcx, 1
	jne 211b
23:
	jmp 21f
20:
	mov ecx, 32
212:
	movzx eax, WORD PTR [rdi]
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 3
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 6
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+8], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 1
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+12], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 4
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+16], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 7
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+20], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 10
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+24], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 13
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+28], r11d
	add rdi, 3
	add rsi, 32
	sub rcx, 1
	jne 212b
21:
	ret
	.p2align 6

vg_mldsa_unpack_t1:
	mov ecx, 64
20:
	mov eax, DWORD PTR [rdi]
	and eax, 1023
	ror eax, 19
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rdi+1]
	shr eax, 2
	and eax, 1023
	ror eax, 19
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rdi+1]
	shr eax, 12
	and eax, 1023
	ror eax, 19
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rdi+1]
	shr eax, 22
	and eax, 1023
	ror eax, 19
	mov DWORD PTR [rsi+12], eax
	add rdi, 5
	add rsi, 16
	sub rcx, 1
	jne 20b
	ret
	.p2align 6

vg_mldsa_hint_bit_pack:
	mov edx, edx
	mov eax, 0
	mov r9, rcx
	mov r10, r8
20:
	mov BYTE PTR [r9], al
	add r9, 1
	sub r10, 1
	jne 20b
	mov r9, rcx
	add r9, rdx
	mov r10, r8
	sub r10, rdx
21:
	mov r11d, 0
22:
	mov esi, DWORD PTR [rdi]
	cmp esi, 0
	jne 23f
	jmp 24f
23:
	mov BYTE PTR [rcx+rax*1], r11b
	add rax, 1
24:
	add rdi, 4
	add r11, 1
	cmp r11d, 256
	jne 22b
	mov BYTE PTR [r9], al
	add r9, 1
	sub r10, 1
	jne 21b
	ret
	.p2align 6

vg_mldsa_hint_bit_unpack:
	mov edx, edx
	mov eax, 0
	mov r9, rcx
	mov r10, r8
20:
	mov DWORD PTR [r9], eax
	add r9, 4
	sub r10, 1
	jne 20b
	mov r9, rdi
	add r9, rdx
	mov r10, rsi
	sub r10, rdx
21:
	cmp rdx, rax
	jae 22f
	jmp 23f
22:
	movzx r11d, BYTE PTR [r9]
	cmp r11, rax
	jb 24f
	cmp rdx, r11
	jb 26f
	cmp rax, r11
	jb 28f
	jmp 29f
28:
	movzx esi, BYTE PTR [rdi+rax*1]
	mov r8d, 1
	mov DWORD PTR [rcx+rsi*4], r8d
	add rax, 1
	cmp rax, r11
	jb 210f
	jmp 211f
210:
212:
	movzx r8d, BYTE PTR [rdi+rax*1-1]
	movzx esi, BYTE PTR [rdi+rax*1]
	cmp r8, rsi
	jb 213f
	mov eax, 256
	jmp 214f
213:
	mov r8d, 1
	mov DWORD PTR [rcx+rsi*4], r8d
	add rax, 1
214:
	cmp rax, r11
	jb 212b
211:
29:
	jmp 27f
26:
	mov eax, 256
27:
	jmp 25f
24:
	mov eax, 256
25:
23:
	add r9, 1
	add rcx, 1024
	sub r10, 1
	jne 21b
	cmp rax, rdx
	jb 215f
	jmp 216f
215:
217:
	movzx r8d, BYTE PTR [rdi+rax*1]
	cmp r8d, 0
	jne 218f
	add rax, 1
	jmp 219f
218:
	mov eax, 256
219:
	cmp rax, rdx
	jb 217b
216:
	cmp rdx, rax
	mov eax, 1
	sbb eax, 0
	ret
	.p2align 6

vg_mldsa_power2round:
	mov ecx, 256
20:
	mov eax, DWORD PTR [rdi+rcx*4-4]
	add rax, 4095
	mov r8, rax
	shr r8, 13
	mov DWORD PTR [rsi+rcx*4-4], r8d
	and rax, 8191
	sub rax, 4095
	sbb r9, r9
	and r9, 8380417
	add rax, r9
	mov DWORD PTR [rdx+rcx*4-4], eax
	sub rcx, 1
	jne 20b
	ret
	.p2align 6

vg_mldsa_high_bits:
	mov esi, esi
	cmp esi, 261888
	mov r10, rdx
	je 20f
	mov ecx, 256
22:
	mov eax, DWORD PTR [rdi+rcx*4-4]
	add rax, 127
	shr rax, 7
	mov r8d, 11275
	mul r8
	add rax, 8388608
	shr rax, 24
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	mov DWORD PTR [r10+rcx*4-4], eax
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov ecx, 256
23:
	mov eax, DWORD PTR [rdi+rcx*4-4]
	add rax, 127
	shr rax, 7
	mov r8d, 1025
	mul r8
	add rax, 2097152
	shr rax, 22
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	mov DWORD PTR [r10+rcx*4-4], eax
	sub rcx, 1
	jne 23b
21:
	ret
	.p2align 6

vg_mldsa_low_bits:
	mov esi, esi
	cmp esi, 261888
	mov r10, rdx
	je 20f
	mov ecx, 256
22:
	mov eax, DWORD PTR [rdi+rcx*4-4]
	mov r11, rax
	add rax, 127
	shr rax, 7
	mov r8d, 11275
	mul r8
	add rax, 8388608
	shr rax, 24
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	mov r8d, 190464
	mul r8
	sub r11, rax
	sbb r8, r8
	and r8, 8380417
	add r11, r8
	mov DWORD PTR [r10+rcx*4-4], r11d
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov ecx, 256
23:
	mov eax, DWORD PTR [rdi+rcx*4-4]
	mov r11, rax
	add rax, 127
	shr rax, 7
	mov r8d, 1025
	mul r8
	add rax, 2097152
	shr rax, 22
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	mov r8d, 523776
	mul r8
	sub r11, rax
	sbb r8, r8
	and r8, 8380417
	add r11, r8
	mov DWORD PTR [r10+rcx*4-4], r11d
	sub rcx, 1
	jne 23b
21:
	ret
	.p2align 6

vg_mldsa_high_bits_avx2:
	mov esi, esi
	cmp esi, 261888
	mov r10, rdx
	je 20f
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 8388608
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 44
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
22:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 1
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 3
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 11
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 13
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 24
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [r10], ymm0
	add rdi, 32
	add r10, 32
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 2097152
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 16
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
23:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 22
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [r10], ymm0
	add rdi, 32
	add r10, 32
	sub rcx, 1
	jne 23b
21:
	vzeroupper
	ret
	.p2align 6

vg_mldsa_low_bits_avx2:
	mov esi, esi
	cmp esi, 261888
	mov r10, rdx
	je 20f
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 8388608
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 44
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
22:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 1
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 3
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 11
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 13
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 24
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 13
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 14
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 17
	vpaddd ymm1, ymm1, ymm2
	vpsubd ymm3, ymm3, ymm1
	vpsrad ymm1, ymm3, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm3, ymm3, ymm1
	vmovdqu YMMWORD PTR [r10], ymm3
	add rdi, 32
	add r10, 32
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 2097152
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 16
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
23:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 22
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vpslld ymm1, ymm0, 19
	vpslld ymm2, ymm0, 9
	vpsubd ymm1, ymm1, ymm2
	vpsubd ymm3, ymm3, ymm1
	vpsrad ymm1, ymm3, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm3, ymm3, ymm1
	vmovdqu YMMWORD PTR [r10], ymm3
	add rdi, 32
	add r10, 32
	sub rcx, 1
	jne 23b
21:
	vzeroupper
	ret
	.p2align 6

vg_mldsa_norm_lt:
	mov esi, esi
	mov r9, -1
	mov ecx, 256
20:
	mov eax, DWORD PTR [rdi+rcx*4-4]
	mov edx, 8380417
	sub rdx, rax
	sub rax, rsi
	sub rdx, rsi
	or rax, rdx
	and r9, rax
	sub rcx, 1
	jne 20b
	mov rax, r9
	shr rax, 63
	ret
	.p2align 6

vg_mldsa_make_hint:
	mov edx, edx
	cmp edx, 261888
	mov r10, rcx
	mov r9d, 0
	je 20f
	mov ecx, 256
22:
	mov eax, DWORD PTR [rsi+rcx*4-4]
	add rax, 127
	shr rax, 7
	mov r8d, 11275
	mul r8
	add rax, 8388608
	shr rax, 24
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	mov r11, rax
	mov eax, DWORD PTR [rsi+rcx*4-4]
	add eax, DWORD PTR [rdi+rcx*4-4]
	sub rax, 8380417
	sbb r8, r8
	and r8, 8380417
	add rax, r8
	add rax, 127
	shr rax, 7
	mov r8d, 11275
	mul r8
	add rax, 8388608
	shr rax, 24
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	xor rax, r11
	add rax, 63
	shr rax, 6
	mov DWORD PTR [r10+rcx*4-4], eax
	add r9, rax
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov ecx, 256
23:
	mov eax, DWORD PTR [rsi+rcx*4-4]
	add rax, 127
	shr rax, 7
	mov r8d, 1025
	mul r8
	add rax, 2097152
	shr rax, 22
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	mov r11, rax
	mov eax, DWORD PTR [rsi+rcx*4-4]
	add eax, DWORD PTR [rdi+rcx*4-4]
	sub rax, 8380417
	sbb r8, r8
	and r8, 8380417
	add rax, r8
	add rax, 127
	shr rax, 7
	mov r8d, 1025
	mul r8
	add rax, 2097152
	shr rax, 22
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	xor rax, r11
	add rax, 63
	shr rax, 6
	mov DWORD PTR [r10+rcx*4-4], eax
	add r9, rax
	sub rcx, 1
	jne 23b
21:
	mov rax, r9
	ret
	.p2align 6

vg_mldsa_norm_lt_avx2:
	mov esi, esi
	cmp esi, 8380417
	jb 20f
	mov esi, 8380417
	jmp 21f
20:
21:
	mov eax, esi
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 8380417
	sub eax, esi
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, -1
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov ecx, 32
22:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpsubd ymm1, ymm0, ymm8
	vpsubd ymm2, ymm9, ymm0
	vpor ymm1, ymm1, ymm2
	vpand ymm10, ymm10, ymm1
	add rdi, 32
	sub rcx, 1
	jne 22b
	vpsrad ymm10, ymm10, 31
	vpmovmskb eax, ymm10
	vzeroupper
	add rax, 1
	shr rax, 32
	ret
	.p2align 6

vg_mldsa_make_hint_avx2:
	mov edx, edx
	cmp edx, 261888
	mov r10, rcx
	mov r9d, 0
	je 20f
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 8388608
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 44
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, 63
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 32
22:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm5, YMMWORD PTR [rdi]
	vmovdqa ymm4, ymm0
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 1
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 3
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 11
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 13
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 24
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm4, ymm5
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 1
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 3
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 11
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 13
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 24
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vpxor ymm0, ymm0, ymm3
	vpaddd ymm0, ymm0, ymm11
	vpsrld ymm0, ymm0, 6
	vpslld ymm1, ymm0, 7
	vmovdqu YMMWORD PTR [r10], ymm0
	vpmovmskb eax, ymm1
	mov edx, eax
	shr edx, 4
	add eax, edx
	mov edx, eax
	shr edx, 8
	add eax, edx
	mov edx, eax
	shr edx, 16
	add eax, edx
	and eax, 15
	add r9, rax
	add rdi, 32
	add rsi, 32
	add r10, 32
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 2097152
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 16
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, 63
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 32
23:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm5, YMMWORD PTR [rdi]
	vmovdqa ymm4, ymm0
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 22
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm4, ymm5
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 22
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vpxor ymm0, ymm0, ymm3
	vpaddd ymm0, ymm0, ymm11
	vpsrld ymm0, ymm0, 6
	vpslld ymm1, ymm0, 7
	vmovdqu YMMWORD PTR [r10], ymm0
	vpmovmskb eax, ymm1
	mov edx, eax
	shr edx, 4
	add eax, edx
	mov edx, eax
	shr edx, 8
	add eax, edx
	mov edx, eax
	shr edx, 16
	add eax, edx
	and eax, 15
	add r9, rax
	add rdi, 32
	add rsi, 32
	add r10, 32
	sub rcx, 1
	jne 23b
21:
	mov rax, r9
	vzeroupper
	ret
	.p2align 6

vg_mldsa_use_hint:
	mov edx, edx
	cmp edx, 261888
	mov r10, rcx
	je 20f
	mov ecx, 256
22:
	mov eax, DWORD PTR [rsi+rcx*4-4]
	mov r11, rax
	add rax, 127
	shr rax, 7
	mov r8d, 11275
	mul r8
	add rax, 8388608
	shr rax, 24
	mov r9, rax
	mov r8d, 190464
	mul r8
	sub rax, r11
	sbb rax, rax
	and rax, 2
	sub rax, 1
	mov r11d, DWORD PTR [rdi+rcx*4-4]
	mov r8d, 0
	sub r8, r11
	sbb r8, r8
	and rax, r8
	add rax, r9
	add rax, 44
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	mov DWORD PTR [r10+rcx*4-4], eax
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov ecx, 256
23:
	mov eax, DWORD PTR [rsi+rcx*4-4]
	mov r11, rax
	add rax, 127
	shr rax, 7
	mov r8d, 1025
	mul r8
	add rax, 2097152
	shr rax, 22
	mov r9, rax
	mov r8d, 523776
	mul r8
	sub rax, r11
	sbb rax, rax
	and rax, 2
	sub rax, 1
	mov r11d, DWORD PTR [rdi+rcx*4-4]
	mov r8d, 0
	sub r8, r11
	sbb r8, r8
	and rax, r8
	add rax, r9
	add rax, 16
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	mov DWORD PTR [r10+rcx*4-4], eax
	sub rcx, 1
	jne 23b
21:
	ret
	.p2align 6

vg_mldsa_use_hint_avx2:
	mov edx, edx
	cmp edx, 261888
	mov r10, rcx
	je 20f
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 8388608
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 44
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
22:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm5, YMMWORD PTR [rdi]
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 1
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 3
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 11
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 13
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 24
	vmovdqa ymm4, ymm0
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 13
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 14
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 17
	vpaddd ymm1, ymm1, ymm2
	vpsubd ymm1, ymm1, ymm3
	vpsrad ymm1, ymm1, 31
	vpaddd ymm1, ymm1, ymm1
	vpxor ymm2, ymm2, ymm2
	vpsubd ymm2, ymm2, ymm5
	vpor ymm2, ymm2, ymm5
	vpsrad ymm2, ymm2, 31
	vpandn ymm1, ymm1, ymm2
	vpaddd ymm4, ymm4, ymm1
	vpaddd ymm4, ymm4, ymm10
	vpsubd ymm4, ymm4, ymm10
	vpsrad ymm1, ymm4, 31
	vpand ymm1, ymm1, ymm10
	vpaddd ymm4, ymm4, ymm1
	vpsubd ymm4, ymm4, ymm10
	vpsrad ymm1, ymm4, 31
	vpand ymm1, ymm1, ymm10
	vpaddd ymm4, ymm4, ymm1
	vmovdqu YMMWORD PTR [r10], ymm4
	add rdi, 32
	add rsi, 32
	add r10, 32
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 2097152
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 16
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
23:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm5, YMMWORD PTR [rdi]
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 22
	vmovdqa ymm4, ymm0
	vpslld ymm1, ymm0, 19
	vpslld ymm2, ymm0, 9
	vpsubd ymm1, ymm1, ymm2
	vpsubd ymm1, ymm1, ymm3
	vpsrad ymm1, ymm1, 31
	vpaddd ymm1, ymm1, ymm1
	vpxor ymm2, ymm2, ymm2
	vpsubd ymm2, ymm2, ymm5
	vpor ymm2, ymm2, ymm5
	vpsrad ymm2, ymm2, 31
	vpandn ymm1, ymm1, ymm2
	vpaddd ymm4, ymm4, ymm1
	vpaddd ymm4, ymm4, ymm10
	vpsubd ymm4, ymm4, ymm10
	vpsrad ymm1, ymm4, 31
	vpand ymm1, ymm1, ymm10
	vpaddd ymm4, ymm4, ymm1
	vpsubd ymm4, ymm4, ymm10
	vpsrad ymm1, ymm4, 31
	vpand ymm1, ymm1, ymm10
	vpaddd ymm4, ymm4, ymm1
	vmovdqu YMMWORD PTR [r10], ymm4
	add rdi, 32
	add rsi, 32
	add r10, 32
	sub rcx, 1
	jne 23b
21:
	vzeroupper
	ret
	.p2align 6

vg_mldsa_rej_ntt_poly:
	mov QWORD PTR [rdx+2024], rbx
	mov QWORD PTR [rdx+2032], rbp
	mov QWORD PTR [rdx+2040], r12
	mov rbx, rdx
	mov rbp, rsi
	mov r12d, 0
	mov rcx, rdi
	mov r8, 34
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rax
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rax
	mov QWORD PTR [rbx+32], rax
	mov QWORD PTR [rbx+40], rax
	mov QWORD PTR [rbx+48], rax
	mov QWORD PTR [rbx+56], rax
	mov QWORD PTR [rbx+64], rax
	mov QWORD PTR [rbx+72], rax
	mov QWORD PTR [rbx+80], rax
	mov QWORD PTR [rbx+88], rax
	mov QWORD PTR [rbx+96], rax
	mov QWORD PTR [rbx+104], rax
	mov QWORD PTR [rbx+112], rax
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+128], rax
	mov QWORD PTR [rbx+136], rax
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rax
	mov QWORD PTR [rbx+160], rax
	mov QWORD PTR [rbx+168], rax
	mov QWORD PTR [rbx+176], rax
	mov QWORD PTR [rbx+184], rax
	mov QWORD PTR [rbx+192], rax
	mov rdi, rbx
	mov esi, 168
	mov edx, 0
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 168
	mov rdx, rax
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 1008
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 336
20:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 21f
	jmp 22f
21:
	cmp r8d, 8380417
	jb 23f
	jmp 24f
23:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
24:
22:
	add rsi, 3
	sub rcx, 1
	jne 20b
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	ret
	.p2align 6

vg_mldsa_rej_ntt_poly4:
	mov QWORD PTR [rdx+4384], rbx
	mov QWORD PTR [rdx+4392], rbp
	mov QWORD PTR [rdx+4400], r12
	mov QWORD PTR [rdx+4408], r13
	mov QWORD PTR [rdx+4416], r14
	mov rbx, rdx
	mov r12, rdi
	mov r13, rsi
	mov r14d, 1
	mov rdi, r12
	add rdi, 0
	mov rsi, r13
	add rsi, 0
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_rej_ntt_poly}
	and r14d, eax
	mov rdi, r12
	add rdi, 34
	mov rsi, r13
	add rsi, 1024
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_rej_ntt_poly}
	and r14d, eax
	mov rdi, r12
	add rdi, 68
	mov rsi, r13
	add rsi, 2048
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_rej_ntt_poly}
	and r14d, eax
	mov rdi, r12
	add rdi, 102
	mov rsi, r13
	add rsi, 3072
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_rej_ntt_poly}
	and r14d, eax
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	ret
	.p2align 6

vg_mldsa_rej_ntt_poly4_avx2:
	mov QWORD PTR [rdx+4384], rbx
	mov QWORD PTR [rdx+4392], rbp
	mov QWORD PTR [rdx+4400], r12
	mov QWORD PTR [rdx+4408], r13
	mov QWORD PTR [rdx+4416], r14
	mov rbx, rdx
	mov r12, rdi
	mov r13, rsi
	mov r14d, 1
	movabs rax, 1
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1600], ymm0
	movabs rax, 32898
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1632], ymm0
	movabs rax, -9223372036854742902
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1664], ymm0
	movabs rax, -9223372034707259392
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1696], ymm0
	movabs rax, 32907
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1728], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1760], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1792], ymm0
	movabs rax, -9223372036854743031
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1824], ymm0
	movabs rax, 138
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1856], ymm0
	movabs rax, 136
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1888], ymm0
	movabs rax, 2147516425
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1920], ymm0
	movabs rax, 2147483658
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1952], ymm0
	movabs rax, 2147516555
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1984], ymm0
	movabs rax, -9223372036854775669
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2016], ymm0
	movabs rax, -9223372036854742903
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2048], ymm0
	movabs rax, -9223372036854743037
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2080], ymm0
	movabs rax, -9223372036854743038
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2112], ymm0
	movabs rax, -9223372036854775680
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2144], ymm0
	movabs rax, 32778
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2176], ymm0
	movabs rax, -9223372034707292150
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2208], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2240], ymm0
	movabs rax, -9223372036854742912
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2272], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2304], ymm0
	movabs rax, -9223372034707259384
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2336], ymm0
	vpxor ymm0, ymm0, ymm0
	vmovdqu YMMWORD PTR [rbx], ymm0
	vmovdqu YMMWORD PTR [rbx+32], ymm0
	vmovdqu YMMWORD PTR [rbx+64], ymm0
	vmovdqu YMMWORD PTR [rbx+96], ymm0
	vmovdqu YMMWORD PTR [rbx+128], ymm0
	vmovdqu YMMWORD PTR [rbx+160], ymm0
	vmovdqu YMMWORD PTR [rbx+192], ymm0
	vmovdqu YMMWORD PTR [rbx+224], ymm0
	vmovdqu YMMWORD PTR [rbx+256], ymm0
	vmovdqu YMMWORD PTR [rbx+288], ymm0
	vmovdqu YMMWORD PTR [rbx+320], ymm0
	vmovdqu YMMWORD PTR [rbx+352], ymm0
	vmovdqu YMMWORD PTR [rbx+384], ymm0
	vmovdqu YMMWORD PTR [rbx+416], ymm0
	vmovdqu YMMWORD PTR [rbx+448], ymm0
	vmovdqu YMMWORD PTR [rbx+480], ymm0
	vmovdqu YMMWORD PTR [rbx+512], ymm0
	vmovdqu YMMWORD PTR [rbx+544], ymm0
	vmovdqu YMMWORD PTR [rbx+576], ymm0
	vmovdqu YMMWORD PTR [rbx+608], ymm0
	vmovdqu YMMWORD PTR [rbx+640], ymm0
	vmovdqu YMMWORD PTR [rbx+672], ymm0
	vmovdqu YMMWORD PTR [rbx+704], ymm0
	vmovdqu YMMWORD PTR [rbx+736], ymm0
	vmovdqu YMMWORD PTR [rbx+768], ymm0
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [rbx], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [rbx+32], rax
	mov rax, QWORD PTR [r12+16]
	mov QWORD PTR [rbx+64], rax
	mov rax, QWORD PTR [r12+24]
	mov QWORD PTR [rbx+96], rax
	movzx eax, BYTE PTR [r12+32]
	mov BYTE PTR [rbx+128], al
	movzx eax, BYTE PTR [r12+33]
	mov BYTE PTR [rbx+129], al
	mov rax, QWORD PTR [r12+34]
	mov QWORD PTR [rbx+8], rax
	mov rax, QWORD PTR [r12+42]
	mov QWORD PTR [rbx+40], rax
	mov rax, QWORD PTR [r12+50]
	mov QWORD PTR [rbx+72], rax
	mov rax, QWORD PTR [r12+58]
	mov QWORD PTR [rbx+104], rax
	movzx eax, BYTE PTR [r12+66]
	mov BYTE PTR [rbx+136], al
	movzx eax, BYTE PTR [r12+67]
	mov BYTE PTR [rbx+137], al
	mov rax, QWORD PTR [r12+68]
	mov QWORD PTR [rbx+16], rax
	mov rax, QWORD PTR [r12+76]
	mov QWORD PTR [rbx+48], rax
	mov rax, QWORD PTR [r12+84]
	mov QWORD PTR [rbx+80], rax
	mov rax, QWORD PTR [r12+92]
	mov QWORD PTR [rbx+112], rax
	movzx eax, BYTE PTR [r12+100]
	mov BYTE PTR [rbx+144], al
	movzx eax, BYTE PTR [r12+101]
	mov BYTE PTR [rbx+145], al
	mov rax, QWORD PTR [r12+102]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [r12+110]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [r12+118]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [r12+126]
	mov QWORD PTR [rbx+120], rax
	movzx eax, BYTE PTR [r12+134]
	mov BYTE PTR [rbx+152], al
	movzx eax, BYTE PTR [r12+135]
	mov BYTE PTR [rbx+153], al
	mov eax, 31
	mov BYTE PTR [rbx+130], al
	mov BYTE PTR [rbx+138], al
	mov BYTE PTR [rbx+146], al
	mov BYTE PTR [rbx+154], al
	mov eax, 128
	mov BYTE PTR [rbx+647], al
	mov BYTE PTR [rbx+655], al
	mov BYTE PTR [rbx+663], al
	mov BYTE PTR [rbx+671], al
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 3
20:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 800
	mov rdx, rbx
	add rdx, 1600
	mov rcx, rbx
	add rcx, 2368
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
21:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 21b
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+64]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+96]
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+128]
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+160]
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+192]
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+224]
	mov QWORD PTR [rbp+56], rax
	mov rax, QWORD PTR [rbx+256]
	mov QWORD PTR [rbp+64], rax
	mov rax, QWORD PTR [rbx+288]
	mov QWORD PTR [rbp+72], rax
	mov rax, QWORD PTR [rbx+320]
	mov QWORD PTR [rbp+80], rax
	mov rax, QWORD PTR [rbx+352]
	mov QWORD PTR [rbp+88], rax
	mov rax, QWORD PTR [rbx+384]
	mov QWORD PTR [rbp+96], rax
	mov rax, QWORD PTR [rbx+416]
	mov QWORD PTR [rbp+104], rax
	mov rax, QWORD PTR [rbx+448]
	mov QWORD PTR [rbp+112], rax
	mov rax, QWORD PTR [rbx+480]
	mov QWORD PTR [rbp+120], rax
	mov rax, QWORD PTR [rbx+512]
	mov QWORD PTR [rbp+128], rax
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 20b
	mov eax, 0
	mov QWORD PTR [rbx+4424], rax
	mov QWORD PTR [rbx+4432], rax
	mov QWORD PTR [rbx+4440], rax
	mov QWORD PTR [rbx+4448], rax
	mov rsi, rbx
	add rsi, 2368
	mov rbp, r13
	add rbp, 0
	mov rdi, QWORD PTR [rbx+4424]
	mov r10d, 21
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
22:
	cmp rdi, 249
	jb 23f
	mov ecx, 8
25:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 26f
	jmp 27f
26:
	cmp r8d, 8380417
	jb 28f
	jmp 29f
28:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
29:
27:
	add rsi, 3
	sub rcx, 1
	jne 25b
	jmp 24f
23:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
24:
	sub r10, 1
	jne 22b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov rbp, r13
	add rbp, 1024
	mov rdi, QWORD PTR [rbx+4432]
	mov r10d, 21
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
210:
	cmp rdi, 249
	jb 211f
	mov ecx, 8
213:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 214f
	jmp 215f
214:
	cmp r8d, 8380417
	jb 216f
	jmp 217f
216:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
217:
215:
	add rsi, 3
	sub rcx, 1
	jne 213b
	jmp 212f
211:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
212:
	sub r10, 1
	jne 210b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov rbp, r13
	add rbp, 2048
	mov rdi, QWORD PTR [rbx+4440]
	mov r10d, 21
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
218:
	cmp rdi, 249
	jb 219f
	mov ecx, 8
221:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 222f
	jmp 223f
222:
	cmp r8d, 8380417
	jb 224f
	jmp 225f
224:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
225:
223:
	add rsi, 3
	sub rcx, 1
	jne 221b
	jmp 220f
219:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
220:
	sub r10, 1
	jne 218b
	mov QWORD PTR [rbx+4440], rdi
	mov rsi, rbx
	add rsi, 3880
	mov rbp, r13
	add rbp, 3072
	mov rdi, QWORD PTR [rbx+4448]
	mov r10d, 21
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
226:
	cmp rdi, 249
	jb 227f
	mov ecx, 8
229:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 230f
	jmp 231f
230:
	cmp r8d, 8380417
	jb 232f
	jmp 233f
232:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
233:
231:
	add rsi, 3
	sub rcx, 1
	jne 229b
	jmp 228f
227:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
228:
	sub r10, 1
	jne 226b
	mov QWORD PTR [rbx+4448], rdi
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
234:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 800
	mov rdx, rbx
	add rdx, 1600
	mov rcx, rbx
	add rcx, 2368
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
235:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 235b
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+64]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+96]
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+128]
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+160]
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+192]
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+224]
	mov QWORD PTR [rbp+56], rax
	mov rax, QWORD PTR [rbx+256]
	mov QWORD PTR [rbp+64], rax
	mov rax, QWORD PTR [rbx+288]
	mov QWORD PTR [rbp+72], rax
	mov rax, QWORD PTR [rbx+320]
	mov QWORD PTR [rbp+80], rax
	mov rax, QWORD PTR [rbx+352]
	mov QWORD PTR [rbp+88], rax
	mov rax, QWORD PTR [rbx+384]
	mov QWORD PTR [rbp+96], rax
	mov rax, QWORD PTR [rbx+416]
	mov QWORD PTR [rbp+104], rax
	mov rax, QWORD PTR [rbx+448]
	mov QWORD PTR [rbp+112], rax
	mov rax, QWORD PTR [rbx+480]
	mov QWORD PTR [rbp+120], rax
	mov rax, QWORD PTR [rbx+512]
	mov QWORD PTR [rbp+128], rax
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 234b
	mov rsi, rbx
	add rsi, 2368
	mov rbp, r13
	add rbp, 0
	mov rdi, QWORD PTR [rbx+4424]
	mov r10d, 14
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
236:
	cmp rdi, 249
	jb 237f
	mov ecx, 8
239:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 240f
	jmp 241f
240:
	cmp r8d, 8380417
	jb 242f
	jmp 243f
242:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
243:
241:
	add rsi, 3
	sub rcx, 1
	jne 239b
	jmp 238f
237:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
238:
	sub r10, 1
	jne 236b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov rbp, r13
	add rbp, 1024
	mov rdi, QWORD PTR [rbx+4432]
	mov r10d, 14
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
244:
	cmp rdi, 249
	jb 245f
	mov ecx, 8
247:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 248f
	jmp 249f
248:
	cmp r8d, 8380417
	jb 250f
	jmp 251f
250:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
251:
249:
	add rsi, 3
	sub rcx, 1
	jne 247b
	jmp 246f
245:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
246:
	sub r10, 1
	jne 244b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov rbp, r13
	add rbp, 2048
	mov rdi, QWORD PTR [rbx+4440]
	mov r10d, 14
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
252:
	cmp rdi, 249
	jb 253f
	mov ecx, 8
255:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 256f
	jmp 257f
256:
	cmp r8d, 8380417
	jb 258f
	jmp 259f
258:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
259:
257:
	add rsi, 3
	sub rcx, 1
	jne 255b
	jmp 254f
253:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
254:
	sub r10, 1
	jne 252b
	mov QWORD PTR [rbx+4440], rdi
	mov rsi, rbx
	add rsi, 3880
	mov rbp, r13
	add rbp, 3072
	mov rdi, QWORD PTR [rbx+4448]
	mov r10d, 14
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
260:
	cmp rdi, 249
	jb 261f
	mov ecx, 8
263:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 264f
	jmp 265f
264:
	cmp r8d, 8380417
	jb 266f
	jmp 267f
266:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
267:
265:
	add rsi, 3
	sub rcx, 1
	jne 263b
	jmp 262f
261:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
262:
	sub r10, 1
	jne 260b
	mov QWORD PTR [rbx+4448], rdi
	mov r14d, 1
	mov rax, QWORD PTR [rbx+4424]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4432]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4440]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4448]
	shr rax, 8
	and r14d, eax
	cmp r14d, 0
	je 268f
	jmp 269f
268:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2704
	mov r10d, 1
270:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 800
	mov rdx, rbx
	add rdx, 1600
	mov rcx, rbx
	add rcx, 2368
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
271:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 271b
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+64]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+96]
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+128]
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+160]
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+192]
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+224]
	mov QWORD PTR [rbp+56], rax
	mov rax, QWORD PTR [rbx+256]
	mov QWORD PTR [rbp+64], rax
	mov rax, QWORD PTR [rbx+288]
	mov QWORD PTR [rbp+72], rax
	mov rax, QWORD PTR [rbx+320]
	mov QWORD PTR [rbp+80], rax
	mov rax, QWORD PTR [rbx+352]
	mov QWORD PTR [rbp+88], rax
	mov rax, QWORD PTR [rbx+384]
	mov QWORD PTR [rbp+96], rax
	mov rax, QWORD PTR [rbx+416]
	mov QWORD PTR [rbp+104], rax
	mov rax, QWORD PTR [rbx+448]
	mov QWORD PTR [rbp+112], rax
	mov rax, QWORD PTR [rbx+480]
	mov QWORD PTR [rbp+120], rax
	mov rax, QWORD PTR [rbx+512]
	mov QWORD PTR [rbp+128], rax
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 270b
	mov rsi, rbx
	add rsi, 2704
	mov rbp, r13
	add rbp, 0
	mov rdi, QWORD PTR [rbx+4424]
	mov r10d, 7
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
272:
	cmp rdi, 249
	jb 273f
	mov ecx, 8
275:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 276f
	jmp 277f
276:
	cmp r8d, 8380417
	jb 278f
	jmp 279f
278:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
279:
277:
	add rsi, 3
	sub rcx, 1
	jne 275b
	jmp 274f
273:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
274:
	sub r10, 1
	jne 272b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 3208
	mov rbp, r13
	add rbp, 1024
	mov rdi, QWORD PTR [rbx+4432]
	mov r10d, 7
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
280:
	cmp rdi, 249
	jb 281f
	mov ecx, 8
283:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 284f
	jmp 285f
284:
	cmp r8d, 8380417
	jb 286f
	jmp 287f
286:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
287:
285:
	add rsi, 3
	sub rcx, 1
	jne 283b
	jmp 282f
281:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
282:
	sub r10, 1
	jne 280b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3712
	mov rbp, r13
	add rbp, 2048
	mov rdi, QWORD PTR [rbx+4440]
	mov r10d, 7
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
288:
	cmp rdi, 249
	jb 289f
	mov ecx, 8
291:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 292f
	jmp 293f
292:
	cmp r8d, 8380417
	jb 294f
	jmp 295f
294:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
295:
293:
	add rsi, 3
	sub rcx, 1
	jne 291b
	jmp 290f
289:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
290:
	sub r10, 1
	jne 288b
	mov QWORD PTR [rbx+4440], rdi
	mov rsi, rbx
	add rsi, 4216
	mov rbp, r13
	add rbp, 3072
	mov rdi, QWORD PTR [rbx+4448]
	mov r10d, 7
	lea r11, {VG_MLDSA_REJ_TBL}
	vmovdqu ymm8, YMMWORD PTR [r11+256]
	vmovdqu ymm9, YMMWORD PTR [r11+288]
	vmovdqu ymm10, YMMWORD PTR [r11+320]
	vmovdqu ymm11, YMMWORD PTR [r11+352]
296:
	cmp rdi, 249
	jb 297f
	mov ecx, 8
299:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 2100f
	jmp 2101f
2100:
	cmp r8d, 8380417
	jb 2102f
	jmp 2103f
2102:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
2103:
2101:
	add rsi, 3
	sub rcx, 1
	jne 299b
	jmp 298f
297:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpand ymm0, ymm0, ymm9
	vpsubd ymm1, ymm0, ymm10
	vpshufb ymm1, ymm1, ymm11
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 15
	shr eax, 16
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rdx*4+384]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*4], xmm0
	add rdi, QWORD PTR [r11+rax*4+384]
	add rsi, 24
298:
	sub r10, 1
	jne 296b
	mov QWORD PTR [rbx+4448], rdi
	mov r14d, 1
	mov rax, QWORD PTR [rbx+4424]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4432]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4440]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4448]
	shr rax, 8
	and r14d, eax
269:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	ret
	.p2align 6

vg_mldsa_rej_bounded_poly:
	mov QWORD PTR [rcx+2024], rbx
	mov QWORD PTR [rcx+2032], rbp
	mov QWORD PTR [rcx+2040], r12
	mov rbx, rcx
	mov rbp, rdx
	mov r12d, esi
	mov rcx, rdi
	mov r8, 66
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rax
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rax
	mov QWORD PTR [rbx+32], rax
	mov QWORD PTR [rbx+40], rax
	mov QWORD PTR [rbx+48], rax
	mov QWORD PTR [rbx+56], rax
	mov QWORD PTR [rbx+64], rax
	mov QWORD PTR [rbx+72], rax
	mov QWORD PTR [rbx+80], rax
	mov QWORD PTR [rbx+88], rax
	mov QWORD PTR [rbx+96], rax
	mov QWORD PTR [rbx+104], rax
	mov QWORD PTR [rbx+112], rax
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+128], rax
	mov QWORD PTR [rbx+136], rax
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rax
	mov QWORD PTR [rbx+160], rax
	mov QWORD PTR [rbx+168], rax
	mov QWORD PTR [rbx+176], rax
	mov QWORD PTR [rbx+184], rax
	mov QWORD PTR [rbx+192], rax
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 544
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	cmp r12d, 2
	je 20f
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 544
22:
	movzx eax, BYTE PTR [rsi]
	mov edx, eax
	and edx, 15
	cmp rdi, 256
	jb 23f
	jmp 24f
23:
	cmp edx, 9
	jb 25f
	jmp 26f
25:
	mov r8d, 4
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
26:
	shr eax, 4
	mov edx, eax
	cmp rdi, 256
	jb 27f
	jmp 28f
27:
	cmp edx, 9
	jb 29f
	jmp 210f
29:
	mov r8d, 4
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
210:
28:
24:
	add rsi, 1
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 544
211:
	movzx eax, BYTE PTR [rsi]
	mov edx, eax
	and edx, 15
	cmp rdi, 256
	jb 212f
	jmp 213f
212:
	cmp edx, 15
	jb 214f
	jmp 215f
214:
	sub edx, 10
	sbb r8d, r8d
	and r8d, 10
	add edx, r8d
	sub edx, 5
	sbb r8d, r8d
	and r8d, 5
	add edx, r8d
	mov r8d, 2
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
215:
	shr eax, 4
	mov edx, eax
	cmp rdi, 256
	jb 216f
	jmp 217f
216:
	cmp edx, 15
	jb 218f
	jmp 219f
218:
	sub edx, 10
	sbb r8d, r8d
	and r8d, 10
	add edx, r8d
	sub edx, 5
	sbb r8d, r8d
	and r8d, 5
	add edx, r8d
	mov r8d, 2
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
219:
217:
213:
	add rsi, 1
	sub rcx, 1
	jne 211b
21:
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	ret
	.p2align 6

vg_mldsa_expand_mask_poly:
	mov QWORD PTR [rcx+2024], rbx
	mov QWORD PTR [rcx+2032], rbp
	mov QWORD PTR [rcx+2040], r12
	mov rbx, rcx
	mov rbp, rdx
	mov r12d, esi
	mov rcx, rdi
	mov r8, 66
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rax
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rax
	mov QWORD PTR [rbx+32], rax
	mov QWORD PTR [rbx+40], rax
	mov QWORD PTR [rbx+48], rax
	mov QWORD PTR [rbx+56], rax
	mov QWORD PTR [rbx+64], rax
	mov QWORD PTR [rbx+72], rax
	mov QWORD PTR [rbx+80], rax
	mov QWORD PTR [rbx+88], rax
	mov QWORD PTR [rbx+96], rax
	mov QWORD PTR [rbx+104], rax
	mov QWORD PTR [rbx+112], rax
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+128], rax
	mov QWORD PTR [rbx+136], rax
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rax
	mov QWORD PTR [rbx+160], rax
	mov QWORD PTR [rbx+168], rax
	mov QWORD PTR [rbx+176], rax
	mov QWORD PTR [rbx+184], rax
	mov QWORD PTR [rbx+192], rax
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 640
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	cmp r12d, 131072
	je 20f
	mov rsi, rbx
	add rsi, 840
	mov rdi, rbp
	mov ecx, 64
22:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov rsi, rbx
	add rsi, 840
	mov rdi, rbp
	mov ecx, 64
23:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 23b
21:
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	ret
	.p2align 6

vg_mldsa_expand_mask_poly4:
	mov QWORD PTR [rcx+5088], rbx
	mov QWORD PTR [rcx+5096], rbp
	mov QWORD PTR [rcx+5104], r12
	mov QWORD PTR [rcx+5112], r13
	mov QWORD PTR [rcx+5120], r14
	mov rbx, rcx
	mov r12, rdi
	mov r13, rdx
	mov r14, rsi
	mov rdi, r12
	add rdi, 0
	mov rsi, r14
	mov rdx, r13
	add rdx, 0
	mov rcx, rbx
	add rcx, 6144
	call {vg_mldsa_expand_mask_poly}
	mov rdi, r12
	add rdi, 66
	mov rsi, r14
	mov rdx, r13
	add rdx, 1024
	mov rcx, rbx
	add rcx, 6144
	call {vg_mldsa_expand_mask_poly}
	mov rdi, r12
	add rdi, 132
	mov rsi, r14
	mov rdx, r13
	add rdx, 2048
	mov rcx, rbx
	add rcx, 6144
	call {vg_mldsa_expand_mask_poly}
	mov rdi, r12
	add rdi, 198
	mov rsi, r14
	mov rdx, r13
	add rdx, 3072
	mov rcx, rbx
	add rcx, 6144
	call {vg_mldsa_expand_mask_poly}
	mov r14, QWORD PTR [rbx+5120]
	mov r13, QWORD PTR [rbx+5112]
	mov r12, QWORD PTR [rbx+5104]
	mov rbp, QWORD PTR [rbx+5096]
	mov rbx, QWORD PTR [rbx+5088]
	ret
	.p2align 6

vg_mldsa_expand_mask_poly4_avx2:
	mov QWORD PTR [rcx+5088], rbx
	mov QWORD PTR [rcx+5096], rbp
	mov QWORD PTR [rcx+5104], r12
	mov QWORD PTR [rcx+5112], r13
	mov QWORD PTR [rcx+5120], r14
	mov rbx, rcx
	mov r12, rdi
	mov r13, rdx
	mov r14, rsi
	movabs rax, 1
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1600], ymm0
	movabs rax, 32898
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1632], ymm0
	movabs rax, -9223372036854742902
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1664], ymm0
	movabs rax, -9223372034707259392
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1696], ymm0
	movabs rax, 32907
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1728], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1760], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1792], ymm0
	movabs rax, -9223372036854743031
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1824], ymm0
	movabs rax, 138
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1856], ymm0
	movabs rax, 136
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1888], ymm0
	movabs rax, 2147516425
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1920], ymm0
	movabs rax, 2147483658
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1952], ymm0
	movabs rax, 2147516555
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1984], ymm0
	movabs rax, -9223372036854775669
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2016], ymm0
	movabs rax, -9223372036854742903
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2048], ymm0
	movabs rax, -9223372036854743037
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2080], ymm0
	movabs rax, -9223372036854743038
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2112], ymm0
	movabs rax, -9223372036854775680
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2144], ymm0
	movabs rax, 32778
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2176], ymm0
	movabs rax, -9223372034707292150
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2208], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2240], ymm0
	movabs rax, -9223372036854742912
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2272], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2304], ymm0
	movabs rax, -9223372034707259384
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2336], ymm0
	vpxor ymm0, ymm0, ymm0
	vmovdqu YMMWORD PTR [rbx], ymm0
	vmovdqu YMMWORD PTR [rbx+32], ymm0
	vmovdqu YMMWORD PTR [rbx+64], ymm0
	vmovdqu YMMWORD PTR [rbx+96], ymm0
	vmovdqu YMMWORD PTR [rbx+128], ymm0
	vmovdqu YMMWORD PTR [rbx+160], ymm0
	vmovdqu YMMWORD PTR [rbx+192], ymm0
	vmovdqu YMMWORD PTR [rbx+224], ymm0
	vmovdqu YMMWORD PTR [rbx+256], ymm0
	vmovdqu YMMWORD PTR [rbx+288], ymm0
	vmovdqu YMMWORD PTR [rbx+320], ymm0
	vmovdqu YMMWORD PTR [rbx+352], ymm0
	vmovdqu YMMWORD PTR [rbx+384], ymm0
	vmovdqu YMMWORD PTR [rbx+416], ymm0
	vmovdqu YMMWORD PTR [rbx+448], ymm0
	vmovdqu YMMWORD PTR [rbx+480], ymm0
	vmovdqu YMMWORD PTR [rbx+512], ymm0
	vmovdqu YMMWORD PTR [rbx+544], ymm0
	vmovdqu YMMWORD PTR [rbx+576], ymm0
	vmovdqu YMMWORD PTR [rbx+608], ymm0
	vmovdqu YMMWORD PTR [rbx+640], ymm0
	vmovdqu YMMWORD PTR [rbx+672], ymm0
	vmovdqu YMMWORD PTR [rbx+704], ymm0
	vmovdqu YMMWORD PTR [rbx+736], ymm0
	vmovdqu YMMWORD PTR [rbx+768], ymm0
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [rbx], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [rbx+32], rax
	mov rax, QWORD PTR [r12+16]
	mov QWORD PTR [rbx+64], rax
	mov rax, QWORD PTR [r12+24]
	mov QWORD PTR [rbx+96], rax
	mov rax, QWORD PTR [r12+32]
	mov QWORD PTR [rbx+128], rax
	mov rax, QWORD PTR [r12+40]
	mov QWORD PTR [rbx+160], rax
	mov rax, QWORD PTR [r12+48]
	mov QWORD PTR [rbx+192], rax
	mov rax, QWORD PTR [r12+56]
	mov QWORD PTR [rbx+224], rax
	movzx eax, BYTE PTR [r12+64]
	mov BYTE PTR [rbx+256], al
	movzx eax, BYTE PTR [r12+65]
	mov BYTE PTR [rbx+257], al
	mov rax, QWORD PTR [r12+66]
	mov QWORD PTR [rbx+8], rax
	mov rax, QWORD PTR [r12+74]
	mov QWORD PTR [rbx+40], rax
	mov rax, QWORD PTR [r12+82]
	mov QWORD PTR [rbx+72], rax
	mov rax, QWORD PTR [r12+90]
	mov QWORD PTR [rbx+104], rax
	mov rax, QWORD PTR [r12+98]
	mov QWORD PTR [rbx+136], rax
	mov rax, QWORD PTR [r12+106]
	mov QWORD PTR [rbx+168], rax
	mov rax, QWORD PTR [r12+114]
	mov QWORD PTR [rbx+200], rax
	mov rax, QWORD PTR [r12+122]
	mov QWORD PTR [rbx+232], rax
	movzx eax, BYTE PTR [r12+130]
	mov BYTE PTR [rbx+264], al
	movzx eax, BYTE PTR [r12+131]
	mov BYTE PTR [rbx+265], al
	mov rax, QWORD PTR [r12+132]
	mov QWORD PTR [rbx+16], rax
	mov rax, QWORD PTR [r12+140]
	mov QWORD PTR [rbx+48], rax
	mov rax, QWORD PTR [r12+148]
	mov QWORD PTR [rbx+80], rax
	mov rax, QWORD PTR [r12+156]
	mov QWORD PTR [rbx+112], rax
	mov rax, QWORD PTR [r12+164]
	mov QWORD PTR [rbx+144], rax
	mov rax, QWORD PTR [r12+172]
	mov QWORD PTR [rbx+176], rax
	mov rax, QWORD PTR [r12+180]
	mov QWORD PTR [rbx+208], rax
	mov rax, QWORD PTR [r12+188]
	mov QWORD PTR [rbx+240], rax
	movzx eax, BYTE PTR [r12+196]
	mov BYTE PTR [rbx+272], al
	movzx eax, BYTE PTR [r12+197]
	mov BYTE PTR [rbx+273], al
	mov rax, QWORD PTR [r12+198]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [r12+206]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [r12+214]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [r12+222]
	mov QWORD PTR [rbx+120], rax
	mov rax, QWORD PTR [r12+230]
	mov QWORD PTR [rbx+152], rax
	mov rax, QWORD PTR [r12+238]
	mov QWORD PTR [rbx+184], rax
	mov rax, QWORD PTR [r12+246]
	mov QWORD PTR [rbx+216], rax
	mov rax, QWORD PTR [r12+254]
	mov QWORD PTR [rbx+248], rax
	movzx eax, BYTE PTR [r12+262]
	mov BYTE PTR [rbx+280], al
	movzx eax, BYTE PTR [r12+263]
	mov BYTE PTR [rbx+281], al
	mov eax, 31
	mov BYTE PTR [rbx+258], al
	mov BYTE PTR [rbx+266], al
	mov BYTE PTR [rbx+274], al
	mov BYTE PTR [rbx+282], al
	mov eax, 128
	mov BYTE PTR [rbx+519], al
	mov BYTE PTR [rbx+527], al
	mov BYTE PTR [rbx+535], al
	mov BYTE PTR [rbx+543], al
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 5
20:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 800
	mov rdx, rbx
	add rdx, 1600
	mov rcx, rbx
	add rcx, 2368
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
21:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 21b
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+64]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+96]
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+128]
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+160]
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+192]
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+224]
	mov QWORD PTR [rbp+56], rax
	mov rax, QWORD PTR [rbx+256]
	mov QWORD PTR [rbp+64], rax
	mov rax, QWORD PTR [rbx+288]
	mov QWORD PTR [rbp+72], rax
	mov rax, QWORD PTR [rbx+320]
	mov QWORD PTR [rbp+80], rax
	mov rax, QWORD PTR [rbx+352]
	mov QWORD PTR [rbp+88], rax
	mov rax, QWORD PTR [rbx+384]
	mov QWORD PTR [rbp+96], rax
	mov rax, QWORD PTR [rbx+416]
	mov QWORD PTR [rbp+104], rax
	mov rax, QWORD PTR [rbx+448]
	mov QWORD PTR [rbp+112], rax
	mov rax, QWORD PTR [rbx+480]
	mov QWORD PTR [rbp+120], rax
	mov rax, QWORD PTR [rbx+512]
	mov QWORD PTR [rbp+128], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+680], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+688], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+696], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+704], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+712], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+720], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+728], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+736], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+744], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+752], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+760], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+768], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+776], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+784], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+792], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+800], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+808], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1360], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1368], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1376], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1384], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1392], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1400], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1408], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1416], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1424], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1432], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1440], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1448], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1456], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1464], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1472], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1480], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1488], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+2040], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+2048], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+2056], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+2064], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+2072], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+2080], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+2088], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+2096], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+2104], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+2112], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+2120], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+2128], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+2136], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+2144], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+2152], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+2160], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+2168], rax
	add rbp, 136
	sub r10, 1
	jne 20b
	vzeroupper
	cmp r14d, 131072
	je 22f
	mov rsi, rbx
	add rsi, 2368
	mov rdi, r13
	add rdi, 0
	mov ecx, 64
24:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 24b
	mov rsi, rbx
	add rsi, 3048
	mov rdi, r13
	add rdi, 1024
	mov ecx, 64
25:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 25b
	mov rsi, rbx
	add rsi, 3728
	mov rdi, r13
	add rdi, 2048
	mov ecx, 64
26:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 26b
	mov rsi, rbx
	add rsi, 4408
	mov rdi, r13
	add rdi, 3072
	mov ecx, 64
27:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 27b
	jmp 23f
22:
	mov rsi, rbx
	add rsi, 2368
	mov rdi, r13
	add rdi, 0
	mov ecx, 64
28:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 28b
	mov rsi, rbx
	add rsi, 3048
	mov rdi, r13
	add rdi, 1024
	mov ecx, 64
29:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 29b
	mov rsi, rbx
	add rsi, 3728
	mov rdi, r13
	add rdi, 2048
	mov ecx, 64
210:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 210b
	mov rsi, rbx
	add rsi, 4408
	mov rdi, r13
	add rdi, 3072
	mov ecx, 64
211:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 211b
23:
	mov r14, QWORD PTR [rbx+5120]
	mov r13, QWORD PTR [rbx+5112]
	mov r12, QWORD PTR [rbx+5104]
	mov rbp, QWORD PTR [rbx+5096]
	mov rbx, QWORD PTR [rbx+5088]
	ret
	.p2align 6

vg_mldsa_sample_in_ball:
	mov QWORD PTR [r8+2024], rbx
	mov QWORD PTR [r8+2032], rbp
	mov QWORD PTR [r8+2040], r12
	mov rbx, r8
	mov rbp, rcx
	mov r12d, edx
	mov rcx, rdi
	mov r8, rsi
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rax
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rax
	mov QWORD PTR [rbx+32], rax
	mov QWORD PTR [rbx+40], rax
	mov QWORD PTR [rbx+48], rax
	mov QWORD PTR [rbx+56], rax
	mov QWORD PTR [rbx+64], rax
	mov QWORD PTR [rbx+72], rax
	mov QWORD PTR [rbx+80], rax
	mov QWORD PTR [rbx+88], rax
	mov QWORD PTR [rbx+96], rax
	mov QWORD PTR [rbx+104], rax
	mov QWORD PTR [rbx+112], rax
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+128], rax
	mov QWORD PTR [rbx+136], rax
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rax
	mov QWORD PTR [rbx+160], rax
	mov QWORD PTR [rbx+168], rax
	mov QWORD PTR [rbx+176], rax
	mov QWORD PTR [rbx+184], rax
	mov QWORD PTR [rbx+192], rax
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 272
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov eax, 0
	mov rdi, rbp
	mov ecx, 256
20:
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 20b
	mov r9, QWORD PTR [rbx+840]
	mov edi, 256
	sub edi, r12d
	mov rsi, rbx
	add rsi, 848
	mov ecx, 264
21:
	cmp rdi, 256
	jb 22f
	jmp 23f
22:
	movzx eax, BYTE PTR [rsi]
	cmp rdi, rax
	jb 24f
	mov edx, DWORD PTR [rbp+rax*4]
	mov DWORD PTR [rbp+rdi*4], edx
	test r9, 1
	je 26f
	mov edx, 8380416
	jmp 27f
26:
	mov edx, 1
27:
	mov DWORD PTR [rbp+rax*4], edx
	shr r9, 1
	add rdi, 1
	jmp 25f
24:
25:
23:
	add rsi, 1
	sub rcx, 1
	jne 21b
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	ret
	.p2align 6
