// The functions of `src/internal/vg_mldsa_rej_ntt_poly.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_ntt_poly:
	mov QWORD PTR [rdx+2024], rbx
	mov QWORD PTR [rdx+2032], rbp
	mov QWORD PTR [rdx+2040], r12
	mov rbx, rdx
	mov rbp, rsi
	mov rcx, rdi
	mov r8d, 34
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
	mov esi, 168
	mov edx, 0
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 168
	mov rdx, rax
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 780
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov r12, rax
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 260
20:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 21f
	jmp 22f
21:
	cmp r8d, 8380417
	jb 23f
	jmp 24f
23:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
24:
22:
	add rsi, 3
	sub rcx, 1
	jne 20b
	cmp rdi, 256
	je 25f
	mov QWORD PTR [rbx+2016], rdi
	mov rdi, rbx
	mov esi, 168
	mov rdx, r12
	mov rcx, rbx
	add rcx, 1620
	mov r8d, 228
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rbx+2016]
	mov rsi, rbx
	add rsi, 1620
	mov ecx, 76
	mov r12d, 0
27:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	and r8d, 127
	ror r8d, 16
	ror edx, 24
	add r8d, edx
	add r8d, eax
	cmp rdi, 256
	jb 28f
	jmp 29f
28:
	cmp r8d, 8380417
	jb 210f
	jmp 211f
210:
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
211:
29:
	add rsi, 3
	sub rcx, 1
	jne 27b
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	jmp 26f
25:
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
26:
	ret
	.p2align 6
