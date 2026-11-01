// The functions of `src/internal/vg_argon2_hprime.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_hprime:
	mov QWORD PTR [r8+840], rbp
	mov QWORD PTR [r8+848], r12
	mov QWORD PTR [r8+856], r13
	mov QWORD PTR [r8+864], r14
	mov QWORD PTR [r8+872], r15
	mov QWORD PTR [r8+880], rbx
	mov rbx, r8
	mov r12, rdi
	mov r13, rsi
	mov r14, rdx
	mov r15, rcx
	mov DWORD PTR [rbx+832], ecx
	mov rsi, r15
	cmp rsi, 65
	jb 20f
	mov esi, 64
	jmp 21f
20:
21:
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov esi, 0
	mov rdx, rbx
	add rdx, 832
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	mov esi, 4
	mov rdx, r12
	mov rcx, r13
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	mov rsi, r13
	add rsi, 4
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch}
	cmp r15, 65
	jb 22f
	mov eax, 32
	mov rdx, rbx
	add rdx, 768
24:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 24b
	sub r15, 32
	cmp r15, 65
	jb 25f
27:
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 64
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch}
	mov eax, 32
	mov rdx, rbx
	add rdx, 768
28:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 28b
	sub r15, 32
	cmp r15, 65
	jae 27b
	jmp 26f
25:
26:
	mov rsi, r15
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 64
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch}
	jmp 23f
22:
23:
	mov rax, r15
	mov rdx, rbx
	add rdx, 768
29:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 29b
	mov rbp, QWORD PTR [rbx+840]
	mov r12, QWORD PTR [rbx+848]
	mov r13, QWORD PTR [rbx+856]
	mov r14, QWORD PTR [rbx+864]
	mov r15, QWORD PTR [rbx+872]
	mov rbx, QWORD PTR [rbx+880]
	ret
	.p2align 6
