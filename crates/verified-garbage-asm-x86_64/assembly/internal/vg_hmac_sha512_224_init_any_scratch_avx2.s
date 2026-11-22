// The functions of `src/internal/vg_hmac_sha512_224_init_any_scratch_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_224_init_any_scratch_avx2:
	mov QWORD PTR [r8+1568], rbx
	mov QWORD PTR [r8+1576], rbp
	mov QWORD PTR [r8+1584], r12
	mov QWORD PTR [r8+1592], r13
	mov QWORD PTR [r8+1600], r14
	mov QWORD PTR [r8+1608], r15
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
	add rdi, 2208
	call {vg_sha512_224_init_core}
	mov rdi, r15
	add rdi, 2208
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rdi, r15
	add rdi, 2208
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2456
	mov rcx, r15
	call {vg_sha512_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 2456
	mov ecx, 28
21:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha512_224_init_scratch_avx2}
	mov rbx, QWORD PTR [r15+1568]
	mov rbp, QWORD PTR [r15+1576]
	mov r12, QWORD PTR [r15+1584]
	mov r13, QWORD PTR [r15+1592]
	mov r14, QWORD PTR [r15+1600]
	mov r15, QWORD PTR [r15+1608]
	ret
	.p2align 6
