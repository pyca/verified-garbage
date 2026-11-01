// The functions of `src/internal/vg_mldsa_expand_mask_poly4.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_expand_mask_poly4:
	mov QWORD PTR [rcx+5088], rbx
	mov QWORD PTR [rcx+5096], rbp
	mov QWORD PTR [rcx+5104], r12
	mov QWORD PTR [rcx+5112], r13
	mov QWORD PTR [rcx+5120], r14
	mov rbx, rcx
	mov r12, rdi
	mov r13, rdx
	mov r14, rsi
	mov rdi, r12
	add rdi, 0
	mov rsi, r14
	mov rdx, r13
	add rdx, 0
	mov rcx, rbx
	add rcx, 6144
	call {vg_mldsa_expand_mask_poly}
	mov rdi, r12
	add rdi, 66
	mov rsi, r14
	mov rdx, r13
	add rdx, 1024
	mov rcx, rbx
	add rcx, 6144
	call {vg_mldsa_expand_mask_poly}
	mov rdi, r12
	add rdi, 132
	mov rsi, r14
	mov rdx, r13
	add rdx, 2048
	mov rcx, rbx
	add rcx, 6144
	call {vg_mldsa_expand_mask_poly}
	mov rdi, r12
	add rdi, 198
	mov rsi, r14
	mov rdx, r13
	add rdx, 3072
	mov rcx, rbx
	add rcx, 6144
	call {vg_mldsa_expand_mask_poly}
	mov r14, QWORD PTR [rbx+5120]
	mov r13, QWORD PTR [rbx+5112]
	mov r12, QWORD PTR [rbx+5104]
	mov rbp, QWORD PTR [rbx+5096]
	mov rbx, QWORD PTR [rbx+5088]
	ret
	.p2align 6
