// The functions of `src/internal/vg_slhdsa_shake_fors_256f.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_fors_256f:
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
	shr rax, 15
	and rax, 511
	mov QWORD PTR [rbx+31328], rax
	movzx eax, BYTE PTR [rbp+1]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+2]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+3]
	or rax, rcx
	shr rax, 14
	and rax, 511
	mov QWORD PTR [rbx+31336], rax
	movzx eax, BYTE PTR [rbp+2]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+3]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+4]
	or rax, rcx
	shr rax, 13
	and rax, 511
	mov QWORD PTR [rbx+31344], rax
	movzx eax, BYTE PTR [rbp+3]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+4]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+5]
	or rax, rcx
	shr rax, 12
	and rax, 511
	mov QWORD PTR [rbx+31352], rax
	movzx eax, BYTE PTR [rbp+4]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+5]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+6]
	or rax, rcx
	shr rax, 11
	and rax, 511
	mov QWORD PTR [rbx+31360], rax
	movzx eax, BYTE PTR [rbp+5]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+6]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+7]
	or rax, rcx
	shr rax, 10
	and rax, 511
	mov QWORD PTR [rbx+31368], rax
	movzx eax, BYTE PTR [rbp+6]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+7]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+8]
	or rax, rcx
	shr rax, 9
	and rax, 511
	mov QWORD PTR [rbx+31376], rax
	movzx eax, BYTE PTR [rbp+7]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+8]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+9]
	or rax, rcx
	shr rax, 8
	and rax, 511
	mov QWORD PTR [rbx+31384], rax
	movzx eax, BYTE PTR [rbp+9]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+10]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+11]
	or rax, rcx
	shr rax, 15
	and rax, 511
	mov QWORD PTR [rbx+31392], rax
	movzx eax, BYTE PTR [rbp+10]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+11]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+12]
	or rax, rcx
	shr rax, 14
	and rax, 511
	mov QWORD PTR [rbx+31400], rax
	movzx eax, BYTE PTR [rbp+11]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+12]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+13]
	or rax, rcx
	shr rax, 13
	and rax, 511
	mov QWORD PTR [rbx+31408], rax
	movzx eax, BYTE PTR [rbp+12]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+13]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+14]
	or rax, rcx
	shr rax, 12
	and rax, 511
	mov QWORD PTR [rbx+31416], rax
	movzx eax, BYTE PTR [rbp+13]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+14]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+15]
	or rax, rcx
	shr rax, 11
	and rax, 511
	mov QWORD PTR [rbx+31424], rax
	movzx eax, BYTE PTR [rbp+14]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+15]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+16]
	or rax, rcx
	shr rax, 10
	and rax, 511
	mov QWORD PTR [rbx+31432], rax
	movzx eax, BYTE PTR [rbp+15]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+16]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+17]
	or rax, rcx
	shr rax, 9
	and rax, 511
	mov QWORD PTR [rbx+31440], rax
	movzx eax, BYTE PTR [rbp+16]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+17]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+18]
	or rax, rcx
	shr rax, 8
	and rax, 511
	mov QWORD PTR [rbx+31448], rax
	movzx eax, BYTE PTR [rbp+18]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+19]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+20]
	or rax, rcx
	shr rax, 15
	and rax, 511
	mov QWORD PTR [rbx+31456], rax
	movzx eax, BYTE PTR [rbp+19]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+20]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+21]
	or rax, rcx
	shr rax, 14
	and rax, 511
	mov QWORD PTR [rbx+31464], rax
	movzx eax, BYTE PTR [rbp+20]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+21]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+22]
	or rax, rcx
	shr rax, 13
	and rax, 511
	mov QWORD PTR [rbx+31472], rax
	movzx eax, BYTE PTR [rbp+21]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+22]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+23]
	or rax, rcx
	shr rax, 12
	and rax, 511
	mov QWORD PTR [rbx+31480], rax
	movzx eax, BYTE PTR [rbp+22]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+23]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+24]
	or rax, rcx
	shr rax, 11
	and rax, 511
	mov QWORD PTR [rbx+31488], rax
	movzx eax, BYTE PTR [rbp+23]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+24]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+25]
	or rax, rcx
	shr rax, 10
	and rax, 511
	mov QWORD PTR [rbx+31496], rax
	movzx eax, BYTE PTR [rbp+24]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+25]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+26]
	or rax, rcx
	shr rax, 9
	and rax, 511
	mov QWORD PTR [rbx+31504], rax
	movzx eax, BYTE PTR [rbp+25]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+26]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+27]
	or rax, rcx
	shr rax, 8
	and rax, 511
	mov QWORD PTR [rbx+31512], rax
	movzx eax, BYTE PTR [rbp+27]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+28]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+29]
	or rax, rcx
	shr rax, 15
	and rax, 511
	mov QWORD PTR [rbx+31520], rax
	movzx eax, BYTE PTR [rbp+28]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+29]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+30]
	or rax, rcx
	shr rax, 14
	and rax, 511
	mov QWORD PTR [rbx+31528], rax
	movzx eax, BYTE PTR [rbp+29]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+30]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+31]
	or rax, rcx
	shr rax, 13
	and rax, 511
	mov QWORD PTR [rbx+31536], rax
	movzx eax, BYTE PTR [rbp+30]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+31]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+32]
	or rax, rcx
	shr rax, 12
	and rax, 511
	mov QWORD PTR [rbx+31544], rax
	movzx eax, BYTE PTR [rbp+31]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+32]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+33]
	or rax, rcx
	shr rax, 11
	and rax, 511
	mov QWORD PTR [rbx+31552], rax
	movzx eax, BYTE PTR [rbp+32]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+33]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+34]
	or rax, rcx
	shr rax, 10
	and rax, 511
	mov QWORD PTR [rbx+31560], rax
	movzx eax, BYTE PTR [rbp+33]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+34]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+35]
	or rax, rcx
	shr rax, 9
	and rax, 511
	mov QWORD PTR [rbx+31568], rax
	movzx eax, BYTE PTR [rbp+34]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+35]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+36]
	or rax, rcx
	shr rax, 8
	and rax, 511
	mov QWORD PTR [rbx+31576], rax
	movzx eax, BYTE PTR [rbp+36]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+37]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+38]
	or rax, rcx
	shr rax, 15
	and rax, 511
	mov QWORD PTR [rbx+31584], rax
	movzx eax, BYTE PTR [rbp+37]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+38]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+39]
	or rax, rcx
	shr rax, 14
	and rax, 511
	mov QWORD PTR [rbx+31592], rax
	movzx eax, BYTE PTR [rbp+38]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+39]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+40]
	or rax, rcx
	shr rax, 13
	and rax, 511
	mov QWORD PTR [rbx+31600], rax
	mov eax, 0
	mov QWORD PTR [rbx+2704], rax
	mov QWORD PTR [rbx+2736], rax
	mov QWORD PTR [rbx+2712], r14
20:
	mov rax, QWORD PTR [rbx+2704]
	mov r13, QWORD PTR [rbx+rax*8+31328]
	mov rsi, QWORD PTR [rbx+2712]
	mov eax, 0
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rax
	mov QWORD PTR [rsi+16], rax
	mov QWORD PTR [rsi+24], rax
	mov QWORD PTR [rsi+32], rax
	mov QWORD PTR [rsi+40], rax
	mov QWORD PTR [rsi+48], rax
	mov QWORD PTR [rsi+56], rax
	mov QWORD PTR [rsi+64], rax
	mov QWORD PTR [rsi+72], rax
	mov QWORD PTR [rsi+80], rax
	mov QWORD PTR [rsi+88], rax
	mov QWORD PTR [rsi+96], rax
	mov QWORD PTR [rsi+104], rax
	mov QWORD PTR [rsi+112], rax
	mov QWORD PTR [rsi+120], rax
	mov QWORD PTR [rsi+128], rax
	mov QWORD PTR [rsi+136], rax
	mov QWORD PTR [rsi+144], rax
	mov QWORD PTR [rsi+152], rax
	mov QWORD PTR [rsi+160], rax
	mov QWORD PTR [rsi+168], rax
	mov QWORD PTR [rsi+176], rax
	mov QWORD PTR [rsi+184], rax
	mov QWORD PTR [rsi+192], rax
	mov QWORD PTR [rsi+200], rax
	mov QWORD PTR [rsi+208], rax
	mov QWORD PTR [rsi+216], rax
	mov QWORD PTR [rsi+224], rax
	mov QWORD PTR [rsi+232], rax
	mov QWORD PTR [rsi+240], rax
	mov QWORD PTR [rsi+248], rax
	mov QWORD PTR [rsi+256], rax
	mov QWORD PTR [rsi+264], rax
	mov QWORD PTR [rsi+272], rax
	mov QWORD PTR [rsi+280], rax
	mov QWORD PTR [rsi+288], rax
	mov QWORD PTR [rsi+296], rax
	mov QWORD PTR [rsi+304], rax
	mov QWORD PTR [rsi+312], rax
	mov QWORD PTR [rbx+2720], rax
21:
	mov eax, 0
	mov QWORD PTR [rbx+2728], rax
22:
	mov r10, QWORD PTR [rbx+2736]
	add r10, QWORD PTR [rbx+2720]
	add r10, QWORD PTR [rbx+2728]
	mov eax, 6
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3348], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3352], eax
	mov r11, r10
	add r11, 0
	mov eax, r11d
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
	mov eax, 6
	bswap eax
	mov DWORD PTR [rbx+3472], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3476], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3480], eax
	mov r11, r10
	add r11, 1
	mov eax, r11d
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
	mov eax, 6
	bswap eax
	mov DWORD PTR [rbx+3600], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3604], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3608], eax
	mov r11, r10
	add r11, 2
	mov eax, r11d
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
	mov eax, 6
	bswap eax
	mov DWORD PTR [rbx+3728], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3732], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3736], eax
	mov r11, r10
	add r11, 3
	mov eax, r11d
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
	call {vg_slhdsa_shake_thash4_n32}
	mov rsi, QWORD PTR [rbx+2712]
	mov rdx, QWORD PTR [rbx+2720]
	add rdx, QWORD PTR [rbx+2728]
	mov rax, rdx
	add rax, 0
	xor rax, r13
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rbx+3360]
	and rax, rdi
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rbx+3368]
	and rax, rdi
	xor rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rbx+3376]
	and rax, rdi
	xor rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rbx+3384]
	and rax, rdi
	xor rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsi+24], rax
	mov rax, rdx
	add rax, 1
	xor rax, r13
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rbx+3488]
	and rax, rdi
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rbx+3496]
	and rax, rdi
	xor rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rbx+3504]
	and rax, rdi
	xor rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rbx+3512]
	and rax, rdi
	xor rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsi+24], rax
	mov rax, rdx
	add rax, 2
	xor rax, r13
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rbx+3616]
	and rax, rdi
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rbx+3624]
	and rax, rdi
	xor rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rbx+3632]
	and rax, rdi
	xor rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rbx+3640]
	and rax, rdi
	xor rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsi+24], rax
	mov rax, rdx
	add rax, 3
	xor rax, r13
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rbx+3744]
	and rax, rdi
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rbx+3752]
	and rax, rdi
	xor rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rbx+3760]
	and rax, rdi
	xor rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rbx+3768]
	and rax, rdi
	xor rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsi+24], rax
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3472], eax
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3600], eax
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3728], eax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 96
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32}
	mov rdx, QWORD PTR [rbx+2728]
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3360]
	mov QWORD PTR [rdx+12640], rax
	mov rax, QWORD PTR [rbx+3368]
	mov QWORD PTR [rdx+12648], rax
	mov rax, QWORD PTR [rbx+3376]
	mov QWORD PTR [rdx+12656], rax
	mov rax, QWORD PTR [rbx+3384]
	mov QWORD PTR [rdx+12664], rax
	mov rax, QWORD PTR [rbx+3488]
	mov QWORD PTR [rdx+12672], rax
	mov rax, QWORD PTR [rbx+3496]
	mov QWORD PTR [rdx+12680], rax
	mov rax, QWORD PTR [rbx+3504]
	mov QWORD PTR [rdx+12688], rax
	mov rax, QWORD PTR [rbx+3512]
	mov QWORD PTR [rdx+12696], rax
	mov rax, QWORD PTR [rbx+3616]
	mov QWORD PTR [rdx+12704], rax
	mov rax, QWORD PTR [rbx+3624]
	mov QWORD PTR [rdx+12712], rax
	mov rax, QWORD PTR [rbx+3632]
	mov QWORD PTR [rdx+12720], rax
	mov rax, QWORD PTR [rbx+3640]
	mov QWORD PTR [rdx+12728], rax
	mov rax, QWORD PTR [rbx+3744]
	mov QWORD PTR [rdx+12736], rax
	mov rax, QWORD PTR [rbx+3752]
	mov QWORD PTR [rdx+12744], rax
	mov rax, QWORD PTR [rbx+3760]
	mov QWORD PTR [rdx+12752], rax
	mov rax, QWORD PTR [rbx+3768]
	mov QWORD PTR [rdx+12760], rax
	mov rax, QWORD PTR [rbx+2728]
	add rax, 4
	mov QWORD PTR [rbx+2728], rax
	cmp rax, 512
	jb 22b
	mov r10, QWORD PTR [rbx+2712]
	add r10, 32
	mov rcx, QWORD PTR [rbx+2736]
	add rcx, QWORD PTR [rbx+2720]
	mov rax, QWORD PTR [rbx+2720]
	mov QWORD PTR [rbx+3000], rax
	mov rax, rcx
	mov QWORD PTR [rbx+3008], rax
	mov rax, 3
	mov QWORD PTR [rbx+3016], rax
	mov rax, r12
	mov QWORD PTR [rbx+3024], rax
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 12640
	mov edx, 512
	mov ecx, 0
	mov r8, r10
	mov r9, r13
	call {vg_slhdsa_shake_levels_n32}
	mov rdx, QWORD PTR [rbx+2720]
	shr rdx, 9
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+12640]
	mov QWORD PTR [rdx+29280], rax
	mov rax, QWORD PTR [rbx+12648]
	mov QWORD PTR [rdx+29288], rax
	mov rax, QWORD PTR [rbx+12656]
	mov QWORD PTR [rdx+29296], rax
	mov rax, QWORD PTR [rbx+12664]
	mov QWORD PTR [rdx+29304], rax
	mov rax, QWORD PTR [rbx+2720]
	add rax, 512
	mov QWORD PTR [rbx+2720], rax
	cmp rax, 512
	jne 21b
	mov rdx, QWORD PTR [rbx+2704]
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+29280]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+29288]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+29296]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+29304]
	mov QWORD PTR [rdx+3896], rax
	mov rax, QWORD PTR [rbx+2712]
	add rax, 320
	mov QWORD PTR [rbx+2712], rax
	mov rax, QWORD PTR [rbx+2736]
	add rax, 512
	mov QWORD PTR [rbx+2736], rax
	mov rax, QWORD PTR [rbx+2704]
	add rax, 1
	mov QWORD PTR [rbx+2704], rax
	cmp rax, 35
	jne 20b
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
	mov edx, 1184
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32}
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
