// The functions of `src/ct.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ct_eq:
	push ebx
	mov eax, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+20]
	cmp eax, edx
	je 20f
	mov eax, 0
	jmp 21f
20:
	mov ebx, 0
	mov ecx, 0
	mov eax, DWORD PTR [esp+12]
	cmp ecx, eax
	je 22f
24:
	mov eax, DWORD PTR [esp+8]
	add eax, ecx
	movzx edx, BYTE PTR [eax]
	mov eax, DWORD PTR [esp+16]
	add eax, ecx
	movzx eax, BYTE PTR [eax]
	xor edx, eax
	or ebx, edx
	add ecx, 1
	mov eax, DWORD PTR [esp+12]
	cmp ecx, eax
	jne 24b
	jmp 23f
22:
23:
	mov eax, ebx
	sub eax, 1
	shr eax, 31
21:
	pop ebx
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-4]
	mov DWORD PTR [esp], ecx
	lea esp, [esp+4]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
