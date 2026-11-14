// The functions of `src/internal/vg_pbkdf2_hmac_sha256_scratch_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha256_scratch_avx2:
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+704], rbx
	mov QWORD PTR [r8+712], rbp
	mov QWORD PTR [r8+720], r12
	mov QWORD PTR [r8+728], r13
	mov QWORD PTR [r8+736], r14
	mov QWORD PTR [r8+744], r15
	mov r15, r8
	mov QWORD PTR [r15+752], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+760], rax
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
	add rdi, 1056
	call {vg_sha256_init_core}
	mov rdi, r15
	add rdi, 1056
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rdi, r15
	add rdi, 1056
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1216
	mov rcx, r15
	call {vg_sha256_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 1216
	mov ecx, 32
21:
	mov rdi, r15
	add rdi, 768
	mov rsi, r15
	add rsi, 864
	mov r8, r15
	call {vg_hmac_sha256_init_scratch_avx2}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+768]
	mov BYTE PTR [r15+r14*1+960], al
	add r14, 1
	cmp r14, 96
	jne 22b
	mov rdi, r15
	add rdi, 960
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rbp, r13
	mov r13, QWORD PTR [r15+752]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+960]
	mov BYTE PTR [r15+r14*1+1056], al
	add r14, 1
	cmp r14, 96
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+1248], eax
	mov rdi, r15
	add rdi, 1056
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 1248
	mov ecx, 4
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rdi, r15
	add rdi, 1056
	mov rsi, r15
	add rsi, 864
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 1152
	mov r8, r15
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+1152]
	mov BYTE PTR [r15+r14*1+1184], al
	add r14, 1
	cmp r14, 32
	jne 27b
	mov rdi, r15
	add rdi, 768
	mov rsi, r15
	add rsi, 1152
	mov rdx, QWORD PTR [r15+760]
	mov rcx, r15
	add rcx, 1184
	mov r8, r15
	call {vg_pbkdf2_hmac_sha256_iterate_avx2}
	mov ecx, 32
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+1184]
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
	mov rbx, QWORD PTR [r15+704]
	mov rbp, QWORD PTR [r15+712]
	mov r12, QWORD PTR [r15+720]
	mov r13, QWORD PTR [r15+728]
	mov r14, QWORD PTR [r15+736]
	mov r15, QWORD PTR [r15+744]
	ret
	.p2align 6
