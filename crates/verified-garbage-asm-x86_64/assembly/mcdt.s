// The functions of `src/mcdt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mcdt_enter:
	push rax
	mov eax, 0
	mov QWORD PTR [rsp], rax
	stmxcsr DWORD PTR [rsp]
	mov eax, DWORD PTR [rsp]
	mov edx, eax
	cmp edx, 8127
	je 20f
	and eax, 65535
	or eax, 63
	mov DWORD PTR [rsp], eax
	ldmxcsr DWORD PTR [rsp]
	lfence
	xor eax, 8127
	mov eax, 1
	mov edx, 0
	cmovne rax, rdx
	jmp 21f
20:
	mov eax, 1
21:
	pop rcx
	pxor xmm0, xmm0
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	ret
	.p2align 6
