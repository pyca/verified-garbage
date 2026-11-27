// The functions of `src/internal/vg_hmac_sha384_init_any_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha384_init_any_scratch:
	mov QWORD PTR [r8+432], rbx
	mov QWORD PTR [r8+440], rbp
	mov QWORD PTR [r8+448], r12
	mov QWORD PTR [r8+456], r13
	mov QWORD PTR [r8+464], r14
	mov QWORD PTR [r8+472], r15
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
	add rdi, 1072
	call {vg_sha384_init_core}
	mov rdi, r15
	add rdi, 1072
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rdi, r15
	add rdi, 1072
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1360
	mov rcx, r15
	call {vg_sha512_finalize_scratch}
	mov rdx, r15
	add rdx, 1360
	mov ecx, 48
21:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha384_init_scratch}
	mov rbx, QWORD PTR [r15+432]
	mov rbp, QWORD PTR [r15+440]
	mov r12, QWORD PTR [r15+448]
	mov r13, QWORD PTR [r15+456]
	mov r14, QWORD PTR [r15+464]
	mov r15, QWORD PTR [r15+472]
	ret
	.p2align 6
