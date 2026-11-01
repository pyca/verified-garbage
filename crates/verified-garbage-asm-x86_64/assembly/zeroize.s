// The functions of `src/zeroize.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_zeroize:
	mov rax, 0
	mov rdx, rsi
	shr rdx, 5
	cmp rdx, 0
	je 20f
22:
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	add rdi, 32
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	mov rdx, rsi
	shr rdx, 3
	and rdx, 3
	cmp rdx, 0
	je 23f
25:
	mov QWORD PTR [rdi], rax
	add rdi, 8
	sub rdx, 1
	jne 25b
	jmp 24f
23:
24:
	mov rdx, rsi
	and rdx, 7
	cmp rdx, 0
	je 26f
28:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub rdx, 1
	jne 28b
	jmp 27f
26:
27:
	ret
	.p2align 6

vg_zeroize_avx:
	vpxor xmm0, xmm0, xmm0
	mov rax, 0
	mov rdx, rsi
	shr rdx, 6
	cmp rdx, 0
	je 20f
22:
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rdi, 64
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	mov rdx, rsi
	shr rdx, 3
	and rdx, 7
	cmp rdx, 0
	je 23f
25:
	mov QWORD PTR [rdi], rax
	add rdi, 8
	sub rdx, 1
	jne 25b
	jmp 24f
23:
24:
	mov rdx, rsi
	and rdx, 7
	cmp rdx, 0
	je 26f
28:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub rdx, 1
	jne 28b
	jmp 27f
26:
27:
	vzeroupper
	ret
	.p2align 6
