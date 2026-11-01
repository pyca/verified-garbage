// The functions of `src/pbkdf2_md5.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_md5:
	lea rsp, [rsp-1048]
	mov rax, QWORD PTR [rsp+1056]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+384], rbx
	mov QWORD PTR [r8+392], rbp
	mov QWORD PTR [r8+400], r12
	mov QWORD PTR [r8+408], r13
	mov QWORD PTR [r8+416], r14
	mov QWORD PTR [r8+424], r15
	mov r15, r8
	mov QWORD PTR [r15+432], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+440], rax
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
	add rdi, 688
	call {vg_md5_init}
	mov rdi, r15
	add rdi, 688
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_md5_update_scratch}
	mov rdi, r15
	add rdi, 688
	mov rsi, rbp
	mov rdx, r15
	add rdx, 800
	mov rcx, r15
	call {vg_md5_finalize_scratch}
	mov rdx, r15
	add rdx, 800
	mov ecx, 16
21:
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 528
	mov r8, r15
	call {vg_hmac_md5_init_scratch}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+448]
	mov BYTE PTR [r15+r14*1+608], al
	add r14, 1
	cmp r14, 80
	jne 22b
	mov rdi, r15
	add rdi, 608
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_md5_update_scratch}
	mov rbp, r13
	mov r13, QWORD PTR [r15+432]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+608]
	mov BYTE PTR [r15+r14*1+688], al
	add r14, 1
	cmp r14, 80
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+816], eax
	mov rdi, r15
	add rdi, 688
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 816
	mov ecx, 4
	mov r8, r15
	call {vg_md5_update_scratch}
	mov rdi, r15
	add rdi, 688
	mov rsi, r15
	add rsi, 528
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 768
	mov r8, r15
	call {vg_hmac_md5_finalize_scratch}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+768]
	mov BYTE PTR [r15+r14*1+784], al
	add r14, 1
	cmp r14, 16
	jne 27b
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 768
	mov rdx, QWORD PTR [r15+440]
	mov rcx, r15
	add rcx, 784
	mov r8, r15
	call {vg_pbkdf2_hmac_md5_iterate}
	mov ecx, 16
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+784]
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
	mov rbx, QWORD PTR [r15+384]
	mov rbp, QWORD PTR [r15+392]
	mov r12, QWORD PTR [r15+400]
	mov r13, QWORD PTR [r15+408]
	mov r14, QWORD PTR [r15+416]
	mov r15, QWORD PTR [r15+424]
	lea rsp, [rsp+1048]
	ret
	.p2align 6
