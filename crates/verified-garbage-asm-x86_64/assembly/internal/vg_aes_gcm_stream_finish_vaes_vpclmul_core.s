// The functions of `src/internal/vg_aes_gcm_stream_finish_vaes_vpclmul_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_stream_finish_vaes_vpclmul_core:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6
