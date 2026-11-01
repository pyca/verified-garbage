// The functions of `src/internal/vg_cmac_aes_finalize.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_finalize:
	cmp r8, 16
	je 20f
	mov eax, 0
	mov QWORD PTR [r9+2048], rax
	mov QWORD PTR [r9+2056], rax
	test r8, r8
	je 22f
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rcx+r10*1]
	mov BYTE PTR [r9+r10*1+2048], al
	add r10, 1
	cmp r10, r8
	jne 24b
	jmp 23f
22:
23:
	mov eax, 128
	mov BYTE PTR [r9+r8*1+2048], al
	mov rax, QWORD PTR [r9+2048]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [r9+2056]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [r9+2056], rax
	jmp 21f
20:
	mov rax, QWORD PTR [rcx]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [rcx+8]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+2056], rax
21:
	mov rax, QWORD PTR [r9+2048]
	xor rax, QWORD PTR [rdx]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [r9+2056]
	xor rax, QWORD PTR [rdx+8]
	mov QWORD PTR [r9+2056], rax
	mov eax, 0
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov rcx, rdx
	mov rdx, r9
	add rdx, 2048
	mov r8d, 1
	call {vg_aes_ctr32}
	ret
	.p2align 6
