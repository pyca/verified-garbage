// The functions of `src/internal/vg_hmac_md5_init_any_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_init_any_scratch:
	mov QWORD PTR [r8+128], rbx
	mov QWORD PTR [r8+136], rbp
	mov QWORD PTR [r8+144], r12
	mov QWORD PTR [r8+152], r13
	mov QWORD PTR [r8+160], r14
	mov QWORD PTR [r8+168], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 65
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 432
	call {vg_md5_init_core}
	mov rdi, r15
	add rdi, 432
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_md5_update_scratch}
	mov rdi, r15
	add rdi, 432
	mov rsi, rbp
	mov rdx, r15
	add rdx, 544
	mov rcx, r15
	call {vg_md5_finalize_scratch}
	mov rdx, r15
	add rdx, 544
	mov ecx, 16
21:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_md5_init_scratch}
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	ret
	.p2align 6
