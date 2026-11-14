// The functions of `src/internal/vg_mldsa65_prepare_signing_key_internal.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_prepare_signing_key_internal:
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
	add rdi, 128
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 4032
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4032
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 256
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 5056
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5056
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 384
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 6080
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6080
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 512
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 7104
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7104
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 640
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 8128
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8128
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 768
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 9152
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 9152
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 896
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 10176
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10176
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1024
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 11200
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11200
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1152
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 12224
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12224
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 13248
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13248
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1408
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 14272
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 14272
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1536
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 15296
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 15296
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1952
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 16320
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16320
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2368
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 17344
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17344
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2784
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 18368
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18368
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 3200
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 19392
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19392
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 3616
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 20416
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20416
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 504
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
