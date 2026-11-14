// The functions of `src/internal/vg_mldsa87_prepare_signing_key_internal_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_prepare_signing_key_internal_avx2:
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
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 4896
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4896
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 224
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 5920
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5920
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 320
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 6944
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6944
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 416
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 7968
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7968
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 512
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 8992
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8992
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 608
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 10016
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10016
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 704
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 11040
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11040
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 800
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 12064
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12064
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 896
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 13088
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13088
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 992
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 14112
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 14112
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1088
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 15136
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 15136
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1184
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 16160
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16160
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 17184
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17184
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1376
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 18208
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18208
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1472
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 19232
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19232
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1568
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 20256
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20256
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1984
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 21280
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 21280
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 2400
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 22304
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 22304
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 2816
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 23328
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 23328
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 3232
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 24352
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 24352
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 3648
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 25376
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 25376
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 4064
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 26400
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 26400
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 4480
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 27424
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 27424
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 612
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
