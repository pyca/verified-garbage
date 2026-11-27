// The functions of `src/internal/vg_hmac_sha1_init_any_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_init_any_scratch:
	mov QWORD PTR [r8+248], rbx
	mov QWORD PTR [r8+256], rbp
	mov QWORD PTR [r8+264], r12
	mov QWORD PTR [r8+272], r13
	mov QWORD PTR [r8+280], r14
	mov QWORD PTR [r8+288], r15
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
	add rdi, 564
	call {vg_sha1_init_core}
	mov rdi, r15
	add rdi, 564
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha1_update_scratch}
	mov rdi, r15
	add rdi, 564
	mov rsi, rbp
	mov rdx, r15
	add rdx, 688
	mov rcx, r15
	call {vg_sha1_finalize_scratch}
	mov rdx, r15
	add rdx, 688
	mov ecx, 20
21:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha1_init_scratch}
	mov rbx, QWORD PTR [r15+248]
	mov rbp, QWORD PTR [r15+256]
	mov r12, QWORD PTR [r15+264]
	mov r13, QWORD PTR [r15+272]
	mov r14, QWORD PTR [r15+280]
	mov r15, QWORD PTR [r15+288]
	ret
	.p2align 6
