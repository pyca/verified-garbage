// The functions of `src/internal/vg_slhdsa_shake_forspk_128f_avx512vl.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_forspk_128f_avx512vl:
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
	shr rax, 18
	and rax, 63
	mov QWORD PTR [rbx+31328], rax
	movzx eax, BYTE PTR [rbp]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+1]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+2]
	or rax, rcx
	shr rax, 12
	and rax, 63
	mov QWORD PTR [rbx+31336], rax
	movzx eax, BYTE PTR [rbp+1]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+2]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+3]
	or rax, rcx
	shr rax, 14
	and rax, 63
	mov QWORD PTR [rbx+31344], rax
	movzx eax, BYTE PTR [rbp+2]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+3]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+4]
	or rax, rcx
	shr rax, 16
	and rax, 63
	mov QWORD PTR [rbx+31352], rax
	movzx eax, BYTE PTR [rbp+3]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+4]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+5]
	or rax, rcx
	shr rax, 18
	and rax, 63
	mov QWORD PTR [rbx+31360], rax
	movzx eax, BYTE PTR [rbp+3]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+4]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+5]
	or rax, rcx
	shr rax, 12
	and rax, 63
	mov QWORD PTR [rbx+31368], rax
	movzx eax, BYTE PTR [rbp+4]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+5]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+6]
	or rax, rcx
	shr rax, 14
	and rax, 63
	mov QWORD PTR [rbx+31376], rax
	movzx eax, BYTE PTR [rbp+5]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+6]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+7]
	or rax, rcx
	shr rax, 16
	and rax, 63
	mov QWORD PTR [rbx+31384], rax
	movzx eax, BYTE PTR [rbp+6]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+7]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+8]
	or rax, rcx
	shr rax, 18
	and rax, 63
	mov QWORD PTR [rbx+31392], rax
	movzx eax, BYTE PTR [rbp+6]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+7]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+8]
	or rax, rcx
	shr rax, 12
	and rax, 63
	mov QWORD PTR [rbx+31400], rax
	movzx eax, BYTE PTR [rbp+7]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+8]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+9]
	or rax, rcx
	shr rax, 14
	and rax, 63
	mov QWORD PTR [rbx+31408], rax
	movzx eax, BYTE PTR [rbp+8]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+9]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+10]
	or rax, rcx
	shr rax, 16
	and rax, 63
	mov QWORD PTR [rbx+31416], rax
	movzx eax, BYTE PTR [rbp+9]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+10]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+11]
	or rax, rcx
	shr rax, 18
	and rax, 63
	mov QWORD PTR [rbx+31424], rax
	movzx eax, BYTE PTR [rbp+9]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+10]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+11]
	or rax, rcx
	shr rax, 12
	and rax, 63
	mov QWORD PTR [rbx+31432], rax
	movzx eax, BYTE PTR [rbp+10]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+11]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+12]
	or rax, rcx
	shr rax, 14
	and rax, 63
	mov QWORD PTR [rbx+31440], rax
	movzx eax, BYTE PTR [rbp+11]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+12]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+13]
	or rax, rcx
	shr rax, 16
	and rax, 63
	mov QWORD PTR [rbx+31448], rax
	movzx eax, BYTE PTR [rbp+12]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+13]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+14]
	or rax, rcx
	shr rax, 18
	and rax, 63
	mov QWORD PTR [rbx+31456], rax
	movzx eax, BYTE PTR [rbp+12]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+13]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+14]
	or rax, rcx
	shr rax, 12
	and rax, 63
	mov QWORD PTR [rbx+31464], rax
	movzx eax, BYTE PTR [rbp+13]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+14]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+15]
	or rax, rcx
	shr rax, 14
	and rax, 63
	mov QWORD PTR [rbx+31472], rax
	movzx eax, BYTE PTR [rbp+14]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+15]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+16]
	or rax, rcx
	shr rax, 16
	and rax, 63
	mov QWORD PTR [rbx+31480], rax
	movzx eax, BYTE PTR [rbp+15]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+16]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+17]
	or rax, rcx
	shr rax, 18
	and rax, 63
	mov QWORD PTR [rbx+31488], rax
	movzx eax, BYTE PTR [rbp+15]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+16]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+17]
	or rax, rcx
	shr rax, 12
	and rax, 63
	mov QWORD PTR [rbx+31496], rax
	movzx eax, BYTE PTR [rbp+16]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+17]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+18]
	or rax, rcx
	shr rax, 14
	and rax, 63
	mov QWORD PTR [rbx+31504], rax
	movzx eax, BYTE PTR [rbp+17]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+18]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+19]
	or rax, rcx
	shr rax, 16
	and rax, 63
	mov QWORD PTR [rbx+31512], rax
	movzx eax, BYTE PTR [rbp+18]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+19]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+20]
	or rax, rcx
	shr rax, 18
	and rax, 63
	mov QWORD PTR [rbx+31520], rax
	movzx eax, BYTE PTR [rbp+18]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+19]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+20]
	or rax, rcx
	shr rax, 12
	and rax, 63
	mov QWORD PTR [rbx+31528], rax
	movzx eax, BYTE PTR [rbp+19]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+20]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+21]
	or rax, rcx
	shr rax, 14
	and rax, 63
	mov QWORD PTR [rbx+31536], rax
	movzx eax, BYTE PTR [rbp+20]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+21]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+22]
	or rax, rcx
	shr rax, 16
	and rax, 63
	mov QWORD PTR [rbx+31544], rax
	movzx eax, BYTE PTR [rbp+21]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+22]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+23]
	or rax, rcx
	shr rax, 18
	and rax, 63
	mov QWORD PTR [rbx+31552], rax
	movzx eax, BYTE PTR [rbp+21]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+22]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+23]
	or rax, rcx
	shr rax, 12
	and rax, 63
	mov QWORD PTR [rbx+31560], rax
	movzx eax, BYTE PTR [rbp+22]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+23]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+24]
	or rax, rcx
	shr rax, 14
	and rax, 63
	mov QWORD PTR [rbx+31568], rax
	movzx eax, BYTE PTR [rbp+23]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+24]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+25]
	or rax, rcx
	shr rax, 16
	and rax, 63
	mov QWORD PTR [rbx+31576], rax
	movzx eax, BYTE PTR [rbp+24]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+25]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+26]
	or rax, rcx
	shr rax, 18
	and rax, 63
	mov QWORD PTR [rbx+31584], rax
	mov eax, 0
	mov QWORD PTR [rbx+2704], rax
	mov QWORD PTR [rbx+2736], rax
	mov QWORD PTR [rbx+2712], r14
20:
	mov r10, QWORD PTR [rbx+2704]
	add r10, 0
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3328], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3332], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3336], eax
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3340], eax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3344], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3352], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 1
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3456], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3460], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3464], eax
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3468], eax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3472], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3480], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 2
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3584], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3588], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3592], eax
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3596], eax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3600], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3608], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 3
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3712], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3716], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3720], eax
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3724], eax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3728], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3736], rax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 64
	mov rcx, rdi
	add rcx, 48
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n16_avx512vl}
	mov eax, 0
	mov QWORD PTR [rbx+2712], rax
21:
	mov r10, QWORD PTR [rbx+2704]
	add r10, 0
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
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
	shl rdx, 4
	add rsi, rdx
	add rsi, 16
	and rax, 1
	je 22f
	mov rax, QWORD PTR [rbx+3344]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rbx+3352]
	mov QWORD PTR [rbx+3368], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3344], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3352], rax
	jmp 23f
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3368], rax
23:
	mov r10, QWORD PTR [rbx+2712]
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3336], eax
	mov rcx, r10
	shr r11, cl
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3340], eax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 1
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
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
	shl rdx, 4
	add rsi, rdx
	add rsi, 16
	and rax, 1
	je 24f
	mov rax, QWORD PTR [rbx+3472]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rbx+3480]
	mov QWORD PTR [rbx+3496], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3472], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3480], rax
	jmp 25f
24:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3496], rax
25:
	mov r10, QWORD PTR [rbx+2712]
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3464], eax
	mov rcx, r10
	shr r11, cl
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3468], eax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 2
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
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
	shl rdx, 4
	add rsi, rdx
	add rsi, 16
	and rax, 1
	je 26f
	mov rax, QWORD PTR [rbx+3600]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rbx+3608]
	mov QWORD PTR [rbx+3624], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3600], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3608], rax
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3624], rax
27:
	mov r10, QWORD PTR [rbx+2712]
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3592], eax
	mov rcx, r10
	shr r11, cl
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3596], eax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 3
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
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
	shl rdx, 4
	add rsi, rdx
	add rsi, 16
	and rax, 1
	je 28f
	mov rax, QWORD PTR [rbx+3728]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rbx+3736]
	mov QWORD PTR [rbx+3752], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3728], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3736], rax
	jmp 29f
28:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3752], rax
29:
	mov r10, QWORD PTR [rbx+2712]
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3720], eax
	mov rcx, r10
	shr r11, cl
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3724], eax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 80
	mov rcx, rdi
	add rcx, 48
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n16_avx512vl}
	mov rax, QWORD PTR [rbx+2712]
	add rax, 1
	mov QWORD PTR [rbx+2712], rax
	cmp rax, 6
	jne 21b
	mov r10, QWORD PTR [rbx+2704]
	add r10, 0
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rdx, r10
	shl rdx, 4
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3344]
	mov QWORD PTR [rdx+3856], rax
	mov rax, QWORD PTR [rbx+3352]
	mov QWORD PTR [rdx+3864], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 1
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rdx, r10
	shl rdx, 4
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3472]
	mov QWORD PTR [rdx+3856], rax
	mov rax, QWORD PTR [rbx+3480]
	mov QWORD PTR [rdx+3864], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 2
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rdx, r10
	shl rdx, 4
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3600]
	mov QWORD PTR [rdx+3856], rax
	mov rax, QWORD PTR [rbx+3608]
	mov QWORD PTR [rdx+3864], rax
	mov r10, QWORD PTR [rbx+2704]
	add r10, 3
	cmp r10, 33
	mov eax, 32
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 32
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	mov r11, QWORD PTR [rbx+r10*8+31328]
	mov rax, r10
	shl rax, 6
	add r11, rax
	mov rsi, r10
	shl rsi, 4
	mov rax, rsi
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, r14
	mov rdx, r10
	shl rdx, 4
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3728]
	mov QWORD PTR [rdx+3856], rax
	mov rax, QWORD PTR [rbx+3736]
	mov QWORD PTR [rdx+3864], rax
	mov rax, QWORD PTR [rbx+2704]
	add rax, 4
	mov QWORD PTR [rbx+2704], rax
	cmp rax, 33
	jb 20b
	mov eax, 4
	bswap eax
	mov DWORD PTR [rbx+3840], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3844], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3848], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3852], eax
	mov rdi, rbx
	add rdi, 3808
	mov esi, 2208
	mov edx, 576
	mov rcx, rdi
	add rcx, 48
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n16_avx512vl}
	mov rax, QWORD PTR [rbx+3856]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rbx+3864]
	mov QWORD PTR [r15+8], rax
	mov r15, QWORD PTR [rbx+2696]
	mov r14, QWORD PTR [rbx+2688]
	mov r13, QWORD PTR [rbx+2680]
	mov r12, QWORD PTR [rbx+2672]
	mov rbp, QWORD PTR [rbx+2664]
	mov rbx, QWORD PTR [rbx+2656]
	ret
	.p2align 6
