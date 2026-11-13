// The functions of `src/internal/vg_aes_gcm_stream_aad_pclmul_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_stream_aad_pclmul_core:
	lea rsp, [rsp-2568]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+128], rbx
	mov QWORD PTR [r9+136], rbp
	mov QWORD PTR [r9+144], r12
	mov QWORD PTR [r9+152], r13
	mov QWORD PTR [r9+160], r14
	mov QWORD PTR [r9+168], r15
	mov r15, r9
	mov r14, rsi
	mov r13, rdi
	mov r12, rcx
	mov rbp, r8
	mov rbx, rdx
	and rbx, 15
	test rbp, rbp
	je 20f
	test rbx, rbx
	je 22f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 24f
	jmp 25f
24:
	mov rcx, rbp
25:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 27f
	jmp 28f
27:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
28:
	jmp 23f
22:
23:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 29f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 210f
29:
210:
	mov rcx, rbp
	test rcx, rcx
	je 211f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6
