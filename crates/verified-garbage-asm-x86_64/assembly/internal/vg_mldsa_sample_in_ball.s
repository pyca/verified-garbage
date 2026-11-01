// The functions of `src/internal/vg_mldsa_sample_in_ball.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_sample_in_ball:
	mov QWORD PTR [r8+2024], rbx
	mov QWORD PTR [r8+2032], rbp
	mov QWORD PTR [r8+2040], r12
	mov rbx, r8
	mov rbp, rcx
	mov r12d, edx
	mov rcx, rdi
	mov r8, rsi
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rax
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rax
	mov QWORD PTR [rbx+32], rax
	mov QWORD PTR [rbx+40], rax
	mov QWORD PTR [rbx+48], rax
	mov QWORD PTR [rbx+56], rax
	mov QWORD PTR [rbx+64], rax
	mov QWORD PTR [rbx+72], rax
	mov QWORD PTR [rbx+80], rax
	mov QWORD PTR [rbx+88], rax
	mov QWORD PTR [rbx+96], rax
	mov QWORD PTR [rbx+104], rax
	mov QWORD PTR [rbx+112], rax
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+128], rax
	mov QWORD PTR [rbx+136], rax
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rax
	mov QWORD PTR [rbx+160], rax
	mov QWORD PTR [rbx+168], rax
	mov QWORD PTR [rbx+176], rax
	mov QWORD PTR [rbx+184], rax
	mov QWORD PTR [rbx+192], rax
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 272
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov eax, 0
	mov rdi, rbp
	mov ecx, 256
20:
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 20b
	mov r9, QWORD PTR [rbx+840]
	mov edi, 256
	sub edi, r12d
	mov rsi, rbx
	add rsi, 848
	mov ecx, 264
21:
	cmp rdi, 256
	jb 22f
	jmp 23f
22:
	movzx eax, BYTE PTR [rsi]
	cmp rdi, rax
	jb 24f
	mov edx, DWORD PTR [rbp+rax*4]
	mov DWORD PTR [rbp+rdi*4], edx
	test r9, 1
	je 26f
	mov edx, 8380416
	jmp 27f
26:
	mov edx, 1
27:
	mov DWORD PTR [rbp+rax*4], edx
	shr r9, 1
	add rdi, 1
	jmp 25f
24:
25:
23:
	add rsi, 1
	sub rcx, 1
	jne 21b
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	ret
	.p2align 6
