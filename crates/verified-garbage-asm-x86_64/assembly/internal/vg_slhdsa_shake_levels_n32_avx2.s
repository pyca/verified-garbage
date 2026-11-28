// The functions of `src/internal/vg_slhdsa_shake_levels_n32_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_levels_n32_avx2:
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
	shl rdx, 5
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
	mov rax, QWORD PTR [rdx+24]
	and rax, rdi
	xor rax, QWORD PTR [r13+24]
	mov QWORD PTR [r13+24], rax
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
	shl rsi, 5
	add rsi, rsi
	add rsi, r12
	mov rdx, QWORD PTR [rbx+3016]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov rdx, QWORD PTR [rbx+3024]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3348], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3352], eax
	mov r11, r9
	add r11, 0
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3356], eax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3368], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3376], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3384], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rbx+3392], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rbx+3400], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rbx+3408], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rbx+3416], rax
	mov rdx, QWORD PTR [rbx+3016]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3472], eax
	mov rdx, QWORD PTR [rbx+3024]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3476], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3480], eax
	mov r11, r9
	add r11, 1
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3484], eax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rbx+3496], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rbx+3504], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rbx+3512], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rbx+3520], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rbx+3528], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rbx+3536], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rbx+3544], rax
	mov rdx, QWORD PTR [rbx+3016]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3600], eax
	mov rdx, QWORD PTR [rbx+3024]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3604], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3608], eax
	mov r11, r9
	add r11, 2
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3612], eax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rbx+3624], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rbx+3632], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rbx+3640], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rbx+3648], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rbx+3656], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rbx+3664], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rbx+3672], rax
	mov rdx, QWORD PTR [rbx+3016]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3728], eax
	mov rdx, QWORD PTR [rbx+3024]
	mov eax, edx
	bswap eax
	mov DWORD PTR [rbx+3732], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3736], eax
	mov r11, r9
	add r11, 3
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3740], eax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rbx+3752], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rbx+3760], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rbx+3768], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rbx+3776], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rbx+3784], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rbx+3792], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rbx+3800], rax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 128
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32_avx2}
	mov rdx, rbp
	shl rdx, 5
	add rdx, r12
	mov rax, QWORD PTR [rbx+3360]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rbx+3368]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rbx+3376]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rbx+3384]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rbx+3488]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rbx+3496]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rbx+3504]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rbx+3512]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rbx+3616]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rbx+3624]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rbx+3632]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rbx+3640]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rbx+3744]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rbx+3752]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rbx+3760]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rbx+3768]
	mov QWORD PTR [rdx+120], rax
	add rbp, 4
	cmp rbp, r15
	jb 22b
	add r13, 32
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
