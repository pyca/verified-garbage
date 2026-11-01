// The functions of `src/internal/vg_mlkem_sample_ntt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sample_ntt:
	mov QWORD PTR [rdx+1680], rbx
	mov QWORD PTR [rdx+1688], rbp
	mov QWORD PTR [rdx+1696], rdi
	mov rbx, rdx
	mov rbp, rsi
	mov rcx, rdi
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
	mov r8d, 34
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 34
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 504
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 168
20:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 21f
	jmp 22f
21:
	mov DWORD PTR [rbp+rdi*4], r9d
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 23f
	jmp 24f
23:
	mov DWORD PTR [rbp+rdi*4], r8d
	cmp r8d, 3329
	adc rdi, 0
24:
22:
	add rsi, 3
	sub rcx, 1
	jne 20b
	cmp rdi, 256
	jb 25f
	jmp 26f
25:
	mov rcx, QWORD PTR [rbx+1696]
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
	mov r8d, 34
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 34
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 840
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 280
27:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 28f
	jmp 29f
28:
	mov DWORD PTR [rbp+rdi*4], r9d
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 210f
	jmp 211f
210:
	mov DWORD PTR [rbp+rdi*4], r8d
	cmp r8d, 3329
	adc rdi, 0
211:
29:
	add rsi, 3
	sub rcx, 1
	jne 27b
26:
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+1688]
	mov rbx, QWORD PTR [rbx+1680]
	ret
	.p2align 6
