// The functions of `src/internal/vg_mldsa_ntt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
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
