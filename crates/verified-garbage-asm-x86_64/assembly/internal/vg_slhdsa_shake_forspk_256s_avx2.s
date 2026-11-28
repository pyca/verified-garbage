// The functions of `src/internal/vg_slhdsa_shake_forspk_256s_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_forspk_256s_avx2:
	mov QWORD PTR [rdi+2656], rbx
	mov QWORD PTR [rdi+2664], rbp
	mov QWORD PTR [rdi+2672], r12
	mov QWORD PTR [rdi+2680], r13
	mov QWORD PTR [rdi+2688], r14
	mov QWORD PTR [rdi+2696], r15
	mov rbx, rdi
	mov r14, rsi
	mov r12, rdx
	mov rbp, rdi
	add rbp, 30304
	mov r15, rdi
	add r15, 30496
	movzx eax, BYTE PTR [rbp]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+1]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+2]
	or rax, rcx
	shr rax, 10
	and rax, 16383
	mov QWORD PTR [rbx+31328], rax
	movzx eax, BYTE PTR [rbp+1]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+2]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+3]
	or rax, rcx
	shr rax, 4
	and rax, 16383
	mov QWORD PTR [rbx+31336], rax
	movzx eax, BYTE PTR [rbp+3]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+4]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+5]
	or rax, rcx
	shr rax, 6
	and rax, 16383
	mov QWORD PTR [rbx+31344], rax
	movzx eax, BYTE PTR [rbp+5]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+6]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+7]
	or rax, rcx
	shr rax, 8
	and rax, 16383
	mov QWORD PTR [rbx+31352], rax
	movzx eax, BYTE PTR [rbp+7]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+8]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+9]
	or rax, rcx
	shr rax, 10
	and rax, 16383
	mov QWORD PTR [rbx+31360], rax
	movzx eax, BYTE PTR [rbp+8]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+9]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+10]
	or rax, rcx
	shr rax, 4
	and rax, 16383
	mov QWORD PTR [rbx+31368], rax
	movzx eax, BYTE PTR [rbp+10]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+11]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+12]
	or rax, rcx
	shr rax, 6
	and rax, 16383
	mov QWORD PTR [rbx+31376], rax
	movzx eax, BYTE PTR [rbp+12]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+13]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+14]
	or rax, rcx
	shr rax, 8
	and rax, 16383
	mov QWORD PTR [rbx+31384], rax
	movzx eax, BYTE PTR [rbp+14]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+15]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+16]
	or rax, rcx
	shr rax, 10
	and rax, 16383
	mov QWORD PTR [rbx+31392], rax
	movzx eax, BYTE PTR [rbp+15]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+16]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+17]
	or rax, rcx
	shr rax, 4
	and rax, 16383
	mov QWORD PTR [rbx+31400], rax
	movzx eax, BYTE PTR [rbp+17]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+18]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+19]
	or rax, rcx
	shr rax, 6
	and rax, 16383
	mov QWORD PTR [rbx+31408], rax
	movzx eax, BYTE PTR [rbp+19]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+20]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+21]
	or rax, rcx
	shr rax, 8
	and rax, 16383
	mov QWORD PTR [rbx+31416], rax
	movzx eax, BYTE PTR [rbp+21]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+22]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+23]
	or rax, rcx
	shr rax, 10
	and rax, 16383
	mov QWORD PTR [rbx+31424], rax
	movzx eax, BYTE PTR [rbp+22]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+23]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+24]
	or rax, rcx
	shr rax, 4
	and rax, 16383
	mov QWORD PTR [rbx+31432], rax
	movzx eax, BYTE PTR [rbp+24]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+25]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+26]
	or rax, rcx
	shr rax, 6
	and rax, 16383
	mov QWORD PTR [rbx+31440], rax
	movzx eax, BYTE PTR [rbp+26]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+27]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+28]
	or rax, rcx
	shr rax, 8
	and rax, 16383
	mov QWORD PTR [rbx+31448], rax
	movzx eax, BYTE PTR [rbp+28]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+29]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+30]
	or rax, rcx
	shr rax, 10
	and rax, 16383
	mov QWORD PTR [rbx+31456], rax
	movzx eax, BYTE PTR [rbp+29]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+30]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+31]
	or rax, rcx
	shr rax, 4
	and rax, 16383
	mov QWORD PTR [rbx+31464], rax
	movzx eax, BYTE PTR [rbp+31]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+32]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+33]
	or rax, rcx
	shr rax, 6
	and rax, 16383
	mov QWORD PTR [rbx+31472], rax
	movzx eax, BYTE PTR [rbp+33]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+34]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+35]
	or rax, rcx
	shr rax, 8
	and rax, 16383
	mov QWORD PTR [rbx+31480], rax
	movzx eax, BYTE PTR [rbp+35]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+36]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+37]
	or rax, rcx
	shr rax, 10
	and rax, 16383
	mov QWORD PTR [rbx+31488], rax
	movzx eax, BYTE PTR [rbp+36]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+37]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+38]
	or rax, rcx
	shr rax, 4
	and rax, 16383
	mov QWORD PTR [rbx+31496], rax
	mov eax, 0
	mov QWORD PTR [rbx+2704], rax
	mov QWORD PTR [rbx+2736], rax
	mov QWORD PTR [rbx+2712], r14
20:
	mov r10, QWORD PTR [rbx+2704]
	add r10, 0
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3348], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3352], eax
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
	mov r10, QWORD PTR [rbx+2704]
	add r10, 1
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3472], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3476], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3480], eax
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3484], eax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3496], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3504], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3512], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 2
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3600], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3604], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3608], eax
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3612], eax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3624], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3632], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3640], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 3
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3728], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3732], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3736], eax
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3740], eax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3752], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3760], rax
	mov rax, QWORD PTR [rsi+24]
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
	mov QWORD PTR [rbx+2712], rax
21:
	mov r10, QWORD PTR [rbx+2704]
	add r10, 0
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rcx, QWORD PTR [rbx+2712]
	mov rax, r11
	shr rax, cl
	mov rdx, QWORD PTR [rbx+2712]
	shl rdx, 5
	add rsi, rdx
	add rsi, 32
	and rax, 1
	je 22f
	mov rax, QWORD PTR [rbx+3360]
	mov QWORD PTR [rbx+3392], rax
	mov rax, QWORD PTR [rbx+3368]
	mov QWORD PTR [rbx+3400], rax
	mov rax, QWORD PTR [rbx+3376]
	mov QWORD PTR [rbx+3408], rax
	mov rax, QWORD PTR [rbx+3384]
	mov QWORD PTR [rbx+3416], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3368], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3376], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3384], rax
	jmp 23f
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3392], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3400], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3408], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3416], rax
23:
	mov r10, QWORD PTR [rbx+2712]
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3352], eax
	mov rcx, r10
	shr r11, cl
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3356], eax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 1
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rcx, QWORD PTR [rbx+2712]
	mov rax, r11
	shr rax, cl
	mov rdx, QWORD PTR [rbx+2712]
	shl rdx, 5
	add rsi, rdx
	add rsi, 32
	and rax, 1
	je 24f
	mov rax, QWORD PTR [rbx+3488]
	mov QWORD PTR [rbx+3520], rax
	mov rax, QWORD PTR [rbx+3496]
	mov QWORD PTR [rbx+3528], rax
	mov rax, QWORD PTR [rbx+3504]
	mov QWORD PTR [rbx+3536], rax
	mov rax, QWORD PTR [rbx+3512]
	mov QWORD PTR [rbx+3544], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3496], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3504], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3512], rax
	jmp 25f
24:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3520], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3528], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3536], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3544], rax
25:
	mov r10, QWORD PTR [rbx+2712]
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3480], eax
	mov rcx, r10
	shr r11, cl
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3484], eax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 2
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rcx, QWORD PTR [rbx+2712]
	mov rax, r11
	shr rax, cl
	mov rdx, QWORD PTR [rbx+2712]
	shl rdx, 5
	add rsi, rdx
	add rsi, 32
	and rax, 1
	je 26f
	mov rax, QWORD PTR [rbx+3616]
	mov QWORD PTR [rbx+3648], rax
	mov rax, QWORD PTR [rbx+3624]
	mov QWORD PTR [rbx+3656], rax
	mov rax, QWORD PTR [rbx+3632]
	mov QWORD PTR [rbx+3664], rax
	mov rax, QWORD PTR [rbx+3640]
	mov QWORD PTR [rbx+3672], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3624], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3632], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3640], rax
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3648], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3656], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3664], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3672], rax
27:
	mov r10, QWORD PTR [rbx+2712]
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3608], eax
	mov rcx, r10
	shr r11, cl
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3612], eax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 3
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rcx, QWORD PTR [rbx+2712]
	mov rax, r11
	shr rax, cl
	mov rdx, QWORD PTR [rbx+2712]
	shl rdx, 5
	add rsi, rdx
	add rsi, 32
	and rax, 1
	je 28f
	mov rax, QWORD PTR [rbx+3744]
	mov QWORD PTR [rbx+3776], rax
	mov rax, QWORD PTR [rbx+3752]
	mov QWORD PTR [rbx+3784], rax
	mov rax, QWORD PTR [rbx+3760]
	mov QWORD PTR [rbx+3792], rax
	mov rax, QWORD PTR [rbx+3768]
	mov QWORD PTR [rbx+3800], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3752], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3760], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3768], rax
	jmp 29f
28:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3776], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3784], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3792], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3800], rax
29:
	mov r10, QWORD PTR [rbx+2712]
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3736], eax
	mov rcx, r10
	shr r11, cl
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3740], eax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 128
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32_avx2}
	mov rax, QWORD PTR [rbx+2712]
	add rax, 1
	mov QWORD PTR [rbx+2712], rax
	cmp rax, 14
	jne 21b
	mov r10, QWORD PTR [rbx+2704]
	add r10, 0
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rdx, r10
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
	mov r10, QWORD PTR [rbx+2704]
	add r10, 1
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rdx, r10
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3488]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+3496]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+3504]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+3512]
	mov QWORD PTR [rdx+3896], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 2
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rdx, r10
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3616]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+3624]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+3632]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+3640]
	mov QWORD PTR [rdx+3896], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 3
	cmp r10, 22
	mov eax, 21
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 21
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 14
	add r11, rax
	mov rsi, r10
	shl rsi, 5
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rdx, r10
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3744]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+3752]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+3760]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+3768]
	mov QWORD PTR [rdx+3896], rax
	mov rax, QWORD PTR [rbx+2704]
	add rax, 4
	mov QWORD PTR [rbx+2704], rax
	cmp rax, 22
	jb 20b
	mov eax, 4
	bswap eax
	mov DWORD PTR [rbx+3856], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3860], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3864], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3868], eax
	mov rdi, rbx
	add rdi, 3808
	mov esi, 2208
	mov edx, 768
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32_avx2}
	mov rax, QWORD PTR [rbx+3872]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rbx+3880]
	mov QWORD PTR [r15+8], rax
	mov rax, QWORD PTR [rbx+3888]
	mov QWORD PTR [r15+16], rax
	mov rax, QWORD PTR [rbx+3896]
	mov QWORD PTR [r15+24], rax
	mov r15, QWORD PTR [rbx+2696]
	mov r14, QWORD PTR [rbx+2688]
	mov r13, QWORD PTR [rbx+2680]
	mov r12, QWORD PTR [rbx+2672]
	mov rbp, QWORD PTR [rbx+2664]
	mov rbx, QWORD PTR [rbx+2656]
	ret
	.p2align 6
