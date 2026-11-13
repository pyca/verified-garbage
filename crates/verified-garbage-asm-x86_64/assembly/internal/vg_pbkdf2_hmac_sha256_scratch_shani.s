// The functions of `src/internal/vg_pbkdf2_hmac_sha256_scratch_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha256_scratch_shani:
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+144], rbx
	mov QWORD PTR [r8+152], rbp
	mov QWORD PTR [r8+160], r12
	mov QWORD PTR [r8+168], r13
	mov QWORD PTR [r8+176], r14
	mov QWORD PTR [r8+184], r15
	mov r15, r8
	mov QWORD PTR [r15+192], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+200], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 65
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 496
	call {vg_sha256_init_core}
	mov rdi, r15
	add rdi, 496
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rdi, r15
	add rdi, 496
	mov rsi, rbp
	mov rdx, r15
	add rdx, 656
	mov rcx, r15
	call {vg_sha256_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 656
	mov ecx, 32
21:
	mov rdi, r15
	add rdi, 208
	mov rsi, r15
	add rsi, 304
	mov r8, r15
	call {vg_hmac_sha256_init_scratch_shani}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+208]
	mov BYTE PTR [r15+r14*1+400], al
	add r14, 1
	cmp r14, 96
	jne 22b
	mov rdi, r15
	add rdi, 400
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rbp, r13
	mov r13, QWORD PTR [r15+192]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+400]
	mov BYTE PTR [r15+r14*1+496], al
	add r14, 1
	cmp r14, 96
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+688], eax
	mov rdi, r15
	add rdi, 496
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 688
	mov ecx, 4
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rdi, r15
	add rdi, 496
	mov rsi, r15
	add rsi, 304
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 592
	mov r8, r15
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+592]
	mov BYTE PTR [r15+r14*1+624], al
	add r14, 1
	cmp r14, 32
	jne 27b
	mov rdi, r15
	add rdi, 208
	mov rsi, r15
	add rsi, 592
	mov rdx, QWORD PTR [r15+200]
	mov rcx, r15
	add rcx, 624
	mov r8, r15
	call {vg_pbkdf2_hmac_sha256_iterate_shani}
	mov ecx, 32
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+624]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	ret
	.p2align 6
