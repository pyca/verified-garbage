// The functions of `src/internal/vg_slhdsa_shake_levels_n24.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_levels_n24:
	mov QWORD PTR [rdi+2912], rbx
	mov QWORD PTR [rdi+2920], rbp
	mov QWORD PTR [rdi+2928], r12
	mov QWORD PTR [rdi+2936], r13
	mov QWORD PTR [rdi+2944], r14
	mov QWORD PTR [rdi+2952], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, rdx
	mov r14, rcx
	mov r13, r8
	mov QWORD PTR [rbx+2960], r9
20:
	mov rcx, r14
	mov rax, QWORD PTR [rbx+2960]
	shr rax, cl
	xor rax, 1
	mov QWORD PTR [rbx+2984], rax
	mov ebp, 0
21:
	mov rax, QWORD PTR [rbx+3000]
	mov rcx, r14
	shr rax, cl
	add rax, rbp
	xor rax, QWORD PTR [rbx+2984]
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rdx, rbp
	mov rcx, rdx
	shl rdx, 4
	shl rcx, 3
	add rdx, rcx
	add rdx, r12
	mov rax, QWORD PTR [rdx]
	and rax, rdi
	xor rax, QWORD PTR [r13]
	mov QWORD PTR [r13], rax
	mov rax, QWORD PTR [rdx+8]
	and rax, rdi
	xor rax, QWORD PTR [r13+8]
	mov QWORD PTR [r13+8], rax
	mov rax, QWORD PTR [rdx+16]
	and rax, rdi
	xor rax, QWORD PTR [r13+16]
	mov QWORD PTR [r13+16], rax
	add rbp, 1
	cmp rbp, r15
	jne 21b
	shr r15, 1
	mov ebp, 0
22:
	mov r10, r14
	add r10, 1
	mov r9, QWORD PTR [rbx+3008]
	mov rcx, r10
	shr r9, cl
	add r9, rbp
	mov rsi, rbp
	mov rcx, rsi
	shl rsi, 4
	shl rcx, 3
	add rsi, rcx
	add rsi, rsi
	add rsi, r12
	mov rdx, QWORD PTR [rbx+3016]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3336], eax
	mov rdx, QWORD PTR [rbx+3024]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3340], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov r11, r9
	add r11, 0
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3348], eax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3352], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3368], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3376], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rbx+3384], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rbx+3392], rax
	mov rdx, QWORD PTR [rbx+3016]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3464], eax
	mov rdx, QWORD PTR [rbx+3024]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3468], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3472], eax
	mov r11, r9
	add r11, 1
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3476], eax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rbx+3480], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rbx+3496], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rbx+3504], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rbx+3512], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rbx+3520], rax
	mov rdx, QWORD PTR [rbx+3016]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3592], eax
	mov rdx, QWORD PTR [rbx+3024]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3596], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3600], eax
	mov r11, r9
	add r11, 2
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3604], eax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rbx+3608], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rbx+3624], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rbx+3632], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rbx+3640], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rbx+3648], rax
	mov rdx, QWORD PTR [rbx+3016]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3720], eax
	mov rdx, QWORD PTR [rbx+3024]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3724], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3728], eax
	mov r11, r9
	add r11, 3
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3732], eax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rbx+3736], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rbx+3752], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rbx+3760], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rbx+3768], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rbx+3776], rax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 104
	mov rcx, rdi
	add rcx, 56
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n24}
	mov rdx, rbp
	mov rcx, rdx
	shl rdx, 4
	shl rcx, 3
	add rdx, rcx
	add rdx, r12
	mov rax, QWORD PTR [rbx+3352]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rbx+3360]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rbx+3368]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rbx+3480]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rbx+3488]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rbx+3496]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rbx+3608]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rbx+3616]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rbx+3624]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rbx+3736]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rbx+3744]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rbx+3752]
	mov QWORD PTR [rdx+88], rax
	add rbp, 4
	cmp rbp, r15
	jb 22b
	add r13, 24
	add r14, 1
	cmp r15, 1
	jne 20b
	mov r15, QWORD PTR [rbx+2952]
	mov r14, QWORD PTR [rbx+2944]
	mov r13, QWORD PTR [rbx+2936]
	mov r12, QWORD PTR [rbx+2928]
	mov rbp, QWORD PTR [rbx+2920]
	mov rbx, QWORD PTR [rbx+2912]
	ret
	.p2align 6
