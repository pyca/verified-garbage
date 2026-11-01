// The functions of `src/internal/vg_mlkem_sample_ntt4.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sample_ntt4:
	mov QWORD PTR [rdx+4384], rbx
	mov QWORD PTR [rdx+4392], rbp
	mov QWORD PTR [rdx+4400], r12
	mov QWORD PTR [rdx+4408], r13
	mov QWORD PTR [rdx+4416], r14
	mov rbx, rdx
	mov r12, rdi
	mov r13, rsi
	mov r14d, 1
	mov rdi, r12
	add rdi, 0
	mov rsi, r13
	add rsi, 0
	mov rdx, rbx
	add rdx, 6144
	call {vg_mlkem_sample_ntt}
	and r14d, eax
	mov rdi, r12
	add rdi, 34
	mov rsi, r13
	add rsi, 1024
	mov rdx, rbx
	add rdx, 6144
	call {vg_mlkem_sample_ntt}
	and r14d, eax
	mov rdi, r12
	add rdi, 68
	mov rsi, r13
	add rsi, 2048
	mov rdx, rbx
	add rdx, 6144
	call {vg_mlkem_sample_ntt}
	and r14d, eax
	mov rdi, r12
	add rdi, 102
	mov rsi, r13
	add rsi, 3072
	mov rdx, rbx
	add rdx, 6144
	call {vg_mlkem_sample_ntt}
	and r14d, eax
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	ret
	.p2align 6
