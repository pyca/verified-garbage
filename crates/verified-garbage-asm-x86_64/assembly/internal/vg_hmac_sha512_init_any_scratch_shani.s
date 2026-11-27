// The functions of `src/internal/vg_hmac_sha512_init_any_scratch_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_init_any_scratch_shani:
	mov QWORD PTR [r8+240], rbx
	mov QWORD PTR [r8+248], rbp
	mov QWORD PTR [r8+256], r12
	mov QWORD PTR [r8+264], r13
	mov QWORD PTR [r8+272], r14
	mov QWORD PTR [r8+280], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 880
	call {vg_sha512_init_core}
	mov rdi, r15
	add rdi, 880
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rdi, r15
	add rdi, 880
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1200
	mov rcx, r15
	call {vg_sha512_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 1200
	mov ecx, 64
21:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha512_init_scratch_shani}
	mov rbx, QWORD PTR [r15+240]
	mov rbp, QWORD PTR [r15+248]
	mov r12, QWORD PTR [r15+256]
	mov r13, QWORD PTR [r15+264]
	mov r14, QWORD PTR [r15+272]
	mov r15, QWORD PTR [r15+280]
	ret
	.p2align 6
