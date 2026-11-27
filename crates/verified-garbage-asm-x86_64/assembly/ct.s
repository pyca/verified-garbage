// The functions of `src/ct.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ct_eq:
	mov rax, 0
	mov r8, rsi
	cmp r8, rcx
	je 20f
	jmp 21f
20:
	mov r8, 0
	cmp r8, rsi
	je 22f
24:
	movzx r9d, BYTE PTR [rdi+r8*1]
	movzx r10d, BYTE PTR [rdx+r8*1]
	xor r9, r10
	or rax, r9
	add r8, 1
	cmp r8, rsi
	jne 24b
	jmp 23f
22:
23:
	sub rax, 1
	shr rax, 63
21:
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6
