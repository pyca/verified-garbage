// The functions of `src/internal/vg_slhdsa_shake_wots4_n32_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_wots4_n32_avx2:
	mov QWORD PTR [rdi+2400], rbx
	mov QWORD PTR [rdi+2408], rbp
	mov QWORD PTR [rdi+2416], r12
	mov QWORD PTR [rdi+2424], r13
	mov QWORD PTR [rdi+2432], r14
	mov QWORD PTR [rdi+2440], r15
	mov rbx, rdi
	mov r12, rsi
	mov r14, rdx
	mov r15, rcx
	mov r10, r12
	add r10, 0
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3348], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3860], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+3856], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3864], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3868], eax
	mov r10, r12
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3476], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+6068], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+6064], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+6072], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+6076], eax
	mov r10, r12
	add r10, 2
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3604], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+8276], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+8272], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+8280], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+8284], eax
	mov r10, r12
	add r10, 3
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3732], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+10484], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+10480], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+10488], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+10492], eax
	mov r13d, 0
20:
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3352], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3356], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3368], rax
	mov rax, QWORD PTR [rbx+3184]
	mov QWORD PTR [rbx+3376], rax
	mov rax, QWORD PTR [rbx+3192]
	mov QWORD PTR [rbx+3384], rax
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3472], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3480], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3484], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3496], rax
	mov rax, QWORD PTR [rbx+3184]
	mov QWORD PTR [rbx+3504], rax
	mov rax, QWORD PTR [rbx+3192]
	mov QWORD PTR [rbx+3512], rax
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3600], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3608], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3612], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3624], rax
	mov rax, QWORD PTR [rbx+3184]
	mov QWORD PTR [rbx+3632], rax
	mov rax, QWORD PTR [rbx+3192]
	mov QWORD PTR [rbx+3640], rax
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3728], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3736], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3740], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3752], rax
	mov rax, QWORD PTR [rbx+3184]
	mov QWORD PTR [rbx+3760], rax
	mov rax, QWORD PTR [rbx+3192]
	mov QWORD PTR [rbx+3768], rax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 96
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32_avx2}
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3472], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3600], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3728], eax
	mov ebp, 0
21:
	movzx ecx, BYTE PTR [rbx+r13*1+30368]
	mov rdx, rbp
	xor rdx, rcx
	mov rsi, r13
	shl rsi, 5
	add rsi, r15
	mov rax, r12
	add rax, 0
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3360]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3368]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3376]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov rcx, QWORD PTR [rbx+3384]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+24], rax
	mov rax, r12
	add rax, 1
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3488]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3496]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3504]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov rcx, QWORD PTR [rbx+3512]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+24], rax
	mov rax, r12
	add rax, 2
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3616]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3624]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3632]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov rcx, QWORD PTR [rbx+3640]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+24], rax
	mov rax, r12
	add rax, 3
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3744]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3752]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3760]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov rcx, QWORD PTR [rbx+3768]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+24], rax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3356], eax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3484], eax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3612], eax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3740], eax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 96
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32_avx2}
	add rbp, 1
	cmp rbp, 15
	jne 21b
	movzx ecx, BYTE PTR [rbx+r13*1+30368]
	mov rdx, rbp
	xor rdx, rcx
	mov rsi, r13
	shl rsi, 5
	add rsi, r15
	mov rax, r12
	add rax, 0
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3360]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3368]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3376]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov rcx, QWORD PTR [rbx+3384]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+24], rax
	mov rax, r12
	add rax, 1
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3488]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3496]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3504]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov rcx, QWORD PTR [rbx+3512]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+24], rax
	mov rax, r12
	add rax, 2
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3616]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3624]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3632]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov rcx, QWORD PTR [rbx+3640]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+24], rax
	mov rax, r12
	add rax, 3
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3744]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3752]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3760]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov rcx, QWORD PTR [rbx+3768]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+24], rax
	mov rdx, r13
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3360]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+3368]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+3376]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+3384]
	mov QWORD PTR [rdx+3896], rax
	mov rax, QWORD PTR [rbx+3488]
	mov QWORD PTR [rdx+6080], rax
	mov rax, QWORD PTR [rbx+3496]
	mov QWORD PTR [rdx+6088], rax
	mov rax, QWORD PTR [rbx+3504]
	mov QWORD PTR [rdx+6096], rax
	mov rax, QWORD PTR [rbx+3512]
	mov QWORD PTR [rdx+6104], rax
	mov rax, QWORD PTR [rbx+3616]
	mov QWORD PTR [rdx+8288], rax
	mov rax, QWORD PTR [rbx+3624]
	mov QWORD PTR [rdx+8296], rax
	mov rax, QWORD PTR [rbx+3632]
	mov QWORD PTR [rdx+8304], rax
	mov rax, QWORD PTR [rbx+3640]
	mov QWORD PTR [rdx+8312], rax
	mov rax, QWORD PTR [rbx+3744]
	mov QWORD PTR [rdx+10496], rax
	mov rax, QWORD PTR [rbx+3752]
	mov QWORD PTR [rdx+10504], rax
	mov rax, QWORD PTR [rbx+3760]
	mov QWORD PTR [rdx+10512], rax
	mov rax, QWORD PTR [rbx+3768]
	mov QWORD PTR [rdx+10520], rax
	add r13, 1
	cmp r13, 67
	jne 20b
	mov rdi, rbx
	add rdi, 3808
	mov esi, 2208
	mov edx, 2208
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32_avx2}
	mov rdx, r12
	shl rdx, 5
	add rdx, rbx
	add rdx, 12640
	mov rax, QWORD PTR [rbx+3872]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rbx+3880]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rbx+3888]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rbx+3896]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rbx+6080]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rbx+6088]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rbx+6096]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rbx+6104]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rbx+8288]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rbx+8296]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rbx+8304]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rbx+8312]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rbx+10496]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rbx+10504]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rbx+10512]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rbx+10520]
	mov QWORD PTR [rdx+120], rax
	mov r15, QWORD PTR [rbx+2440]
	mov r14, QWORD PTR [rbx+2432]
	mov r13, QWORD PTR [rbx+2424]
	mov r12, QWORD PTR [rbx+2416]
	mov rbp, QWORD PTR [rbx+2408]
	mov rbx, QWORD PTR [rbx+2400]
	ret
	.p2align 6
