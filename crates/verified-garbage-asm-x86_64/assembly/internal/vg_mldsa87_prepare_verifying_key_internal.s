// The functions of `src/internal/vg_mldsa87_prepare_verifying_key_internal.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_prepare_verifying_key_internal:
	mov QWORD PTR [rdx+840], rbx
	mov QWORD PTR [rdx+848], rbp
	mov QWORD PTR [rdx+856], r12
	mov QWORD PTR [rdx+864], r13
	mov QWORD PTR [rdx+872], r14
	mov QWORD PTR [rdx+880], r15
	mov rbx, rsi
	mov rbp, rdi
	mov r12, rdx
	mov r13, rdx
	mov rdi, rbp
	add rdi, 32
	mov rsi, rbx
	add rsi, 2592
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 2592
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 3616
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 3616
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 4640
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 4640
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 5664
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 5664
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1312
	mov rsi, rbx
	add rsi, 6688
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 6688
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1632
	mov rsi, rbx
	add rsi, 7712
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 7712
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1952
	mov rsi, rbx
	add rsi, 8736
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 8736
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2272
	mov rsi, rbx
	add rsi, 9760
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 9760
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 324
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rbx, QWORD PTR [r12+840]
	mov rbp, QWORD PTR [r12+848]
	mov r13, QWORD PTR [r12+864]
	mov r14, QWORD PTR [r12+872]
	mov r15, QWORD PTR [r12+880]
	mov r12, QWORD PTR [r12+856]
	ret
	.p2align 6
