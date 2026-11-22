// The functions of `src/internal/vg_hmac_sha224_init_any_scratch_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha224_init_any_scratch_shani:
	mov QWORD PTR [r8+144], rbx
	mov QWORD PTR [r8+152], rbp
	mov QWORD PTR [r8+160], r12
	mov QWORD PTR [r8+168], r13
	mov QWORD PTR [r8+176], r14
	mov QWORD PTR [r8+184], r15
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
	add rdi, 496
	call {vg_sha224_init_core}
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
	add rdx, 648
	mov rcx, r15
	call {vg_sha256_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 648
	mov ecx, 28
21:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha224_init_scratch_shani}
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	ret
	.p2align 6
