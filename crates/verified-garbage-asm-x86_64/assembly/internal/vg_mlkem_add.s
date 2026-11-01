// The functions of `src/internal/vg_mlkem_add.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_add:
	mov eax, 3329
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov ecx, 64
20:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu xmm1, XMMWORD PTR [rsi]
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm1, xmm0
	psrad xmm1, 31
	pand xmm1, xmm15
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rsi, 16
	sub rcx, 1
	jne 20b
	ret
	.p2align 6
