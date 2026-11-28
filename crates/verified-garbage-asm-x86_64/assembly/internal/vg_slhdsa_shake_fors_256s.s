// The functions of `src/internal/vg_slhdsa_shake_fors_256s.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_fors_256s:
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
	mov QWORD PTR [rsi+320], rax
	mov QWORD PTR [rsi+328], rax
	mov QWORD PTR [rsi+336], rax
	mov QWORD PTR [rsi+344], rax
	mov QWORD PTR [rsi+352], rax
	mov QWORD PTR [rsi+360], rax
	mov QWORD PTR [rsi+368], rax
	mov QWORD PTR [rsi+376], rax
	mov QWORD PTR [rsi+384], rax
	mov QWORD PTR [rsi+392], rax
	mov QWORD PTR [rsi+400], rax
	mov QWORD PTR [rsi+408], rax
	mov QWORD PTR [rsi+416], rax
	mov QWORD PTR [rsi+424], rax
	mov QWORD PTR [rsi+432], rax
	mov QWORD PTR [rsi+440], rax
	mov QWORD PTR [rsi+448], rax
	mov QWORD PTR [rsi+456], rax
	mov QWORD PTR [rsi+464], rax
	mov QWORD PTR [rsi+472], rax
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
	cmp rax, 16384
	jne 21b
	mov rax, QWORD PTR [rbx+29280]
	mov QWORD PTR [rbx+12640], rax
	mov rax, QWORD PTR [rbx+29288]
	mov QWORD PTR [rbx+12648], rax
	mov rax, QWORD PTR [rbx+29296]
	mov QWORD PTR [rbx+12656], rax
	mov rax, QWORD PTR [rbx+29304]
	mov QWORD PTR [rbx+12664], rax
	mov rax, QWORD PTR [rbx+29312]
	mov QWORD PTR [rbx+12672], rax
	mov rax, QWORD PTR [rbx+29320]
	mov QWORD PTR [rbx+12680], rax
	mov rax, QWORD PTR [rbx+29328]
	mov QWORD PTR [rbx+12688], rax
	mov rax, QWORD PTR [rbx+29336]
	mov QWORD PTR [rbx+12696], rax
	mov rax, QWORD PTR [rbx+29344]
	mov QWORD PTR [rbx+12704], rax
	mov rax, QWORD PTR [rbx+29352]
	mov QWORD PTR [rbx+12712], rax
	mov rax, QWORD PTR [rbx+29360]
	mov QWORD PTR [rbx+12720], rax
	mov rax, QWORD PTR [rbx+29368]
	mov QWORD PTR [rbx+12728], rax
	mov rax, QWORD PTR [rbx+29376]
	mov QWORD PTR [rbx+12736], rax
	mov rax, QWORD PTR [rbx+29384]
	mov QWORD PTR [rbx+12744], rax
	mov rax, QWORD PTR [rbx+29392]
	mov QWORD PTR [rbx+12752], rax
	mov rax, QWORD PTR [rbx+29400]
	mov QWORD PTR [rbx+12760], rax
	mov rax, QWORD PTR [rbx+29408]
	mov QWORD PTR [rbx+12768], rax
	mov rax, QWORD PTR [rbx+29416]
	mov QWORD PTR [rbx+12776], rax
	mov rax, QWORD PTR [rbx+29424]
	mov QWORD PTR [rbx+12784], rax
	mov rax, QWORD PTR [rbx+29432]
	mov QWORD PTR [rbx+12792], rax
	mov rax, QWORD PTR [rbx+29440]
	mov QWORD PTR [rbx+12800], rax
	mov rax, QWORD PTR [rbx+29448]
	mov QWORD PTR [rbx+12808], rax
	mov rax, QWORD PTR [rbx+29456]
	mov QWORD PTR [rbx+12816], rax
	mov rax, QWORD PTR [rbx+29464]
	mov QWORD PTR [rbx+12824], rax
	mov rax, QWORD PTR [rbx+29472]
	mov QWORD PTR [rbx+12832], rax
	mov rax, QWORD PTR [rbx+29480]
	mov QWORD PTR [rbx+12840], rax
	mov rax, QWORD PTR [rbx+29488]
	mov QWORD PTR [rbx+12848], rax
	mov rax, QWORD PTR [rbx+29496]
	mov QWORD PTR [rbx+12856], rax
	mov rax, QWORD PTR [rbx+29504]
	mov QWORD PTR [rbx+12864], rax
	mov rax, QWORD PTR [rbx+29512]
	mov QWORD PTR [rbx+12872], rax
	mov rax, QWORD PTR [rbx+29520]
	mov QWORD PTR [rbx+12880], rax
	mov rax, QWORD PTR [rbx+29528]
	mov QWORD PTR [rbx+12888], rax
	mov rax, QWORD PTR [rbx+29536]
	mov QWORD PTR [rbx+12896], rax
	mov rax, QWORD PTR [rbx+29544]
	mov QWORD PTR [rbx+12904], rax
	mov rax, QWORD PTR [rbx+29552]
	mov QWORD PTR [rbx+12912], rax
	mov rax, QWORD PTR [rbx+29560]
	mov QWORD PTR [rbx+12920], rax
	mov rax, QWORD PTR [rbx+29568]
	mov QWORD PTR [rbx+12928], rax
	mov rax, QWORD PTR [rbx+29576]
	mov QWORD PTR [rbx+12936], rax
	mov rax, QWORD PTR [rbx+29584]
	mov QWORD PTR [rbx+12944], rax
	mov rax, QWORD PTR [rbx+29592]
	mov QWORD PTR [rbx+12952], rax
	mov rax, QWORD PTR [rbx+29600]
	mov QWORD PTR [rbx+12960], rax
	mov rax, QWORD PTR [rbx+29608]
	mov QWORD PTR [rbx+12968], rax
	mov rax, QWORD PTR [rbx+29616]
	mov QWORD PTR [rbx+12976], rax
	mov rax, QWORD PTR [rbx+29624]
	mov QWORD PTR [rbx+12984], rax
	mov rax, QWORD PTR [rbx+29632]
	mov QWORD PTR [rbx+12992], rax
	mov rax, QWORD PTR [rbx+29640]
	mov QWORD PTR [rbx+13000], rax
	mov rax, QWORD PTR [rbx+29648]
	mov QWORD PTR [rbx+13008], rax
	mov rax, QWORD PTR [rbx+29656]
	mov QWORD PTR [rbx+13016], rax
	mov rax, QWORD PTR [rbx+29664]
	mov QWORD PTR [rbx+13024], rax
	mov rax, QWORD PTR [rbx+29672]
	mov QWORD PTR [rbx+13032], rax
	mov rax, QWORD PTR [rbx+29680]
	mov QWORD PTR [rbx+13040], rax
	mov rax, QWORD PTR [rbx+29688]
	mov QWORD PTR [rbx+13048], rax
	mov rax, QWORD PTR [rbx+29696]
	mov QWORD PTR [rbx+13056], rax
	mov rax, QWORD PTR [rbx+29704]
	mov QWORD PTR [rbx+13064], rax
	mov rax, QWORD PTR [rbx+29712]
	mov QWORD PTR [rbx+13072], rax
	mov rax, QWORD PTR [rbx+29720]
	mov QWORD PTR [rbx+13080], rax
	mov rax, QWORD PTR [rbx+29728]
	mov QWORD PTR [rbx+13088], rax
	mov rax, QWORD PTR [rbx+29736]
	mov QWORD PTR [rbx+13096], rax
	mov rax, QWORD PTR [rbx+29744]
	mov QWORD PTR [rbx+13104], rax
	mov rax, QWORD PTR [rbx+29752]
	mov QWORD PTR [rbx+13112], rax
	mov rax, QWORD PTR [rbx+29760]
	mov QWORD PTR [rbx+13120], rax
	mov rax, QWORD PTR [rbx+29768]
	mov QWORD PTR [rbx+13128], rax
	mov rax, QWORD PTR [rbx+29776]
	mov QWORD PTR [rbx+13136], rax
	mov rax, QWORD PTR [rbx+29784]
	mov QWORD PTR [rbx+13144], rax
	mov rax, QWORD PTR [rbx+29792]
	mov QWORD PTR [rbx+13152], rax
	mov rax, QWORD PTR [rbx+29800]
	mov QWORD PTR [rbx+13160], rax
	mov rax, QWORD PTR [rbx+29808]
	mov QWORD PTR [rbx+13168], rax
	mov rax, QWORD PTR [rbx+29816]
	mov QWORD PTR [rbx+13176], rax
	mov rax, QWORD PTR [rbx+29824]
	mov QWORD PTR [rbx+13184], rax
	mov rax, QWORD PTR [rbx+29832]
	mov QWORD PTR [rbx+13192], rax
	mov rax, QWORD PTR [rbx+29840]
	mov QWORD PTR [rbx+13200], rax
	mov rax, QWORD PTR [rbx+29848]
	mov QWORD PTR [rbx+13208], rax
	mov rax, QWORD PTR [rbx+29856]
	mov QWORD PTR [rbx+13216], rax
	mov rax, QWORD PTR [rbx+29864]
	mov QWORD PTR [rbx+13224], rax
	mov rax, QWORD PTR [rbx+29872]
	mov QWORD PTR [rbx+13232], rax
	mov rax, QWORD PTR [rbx+29880]
	mov QWORD PTR [rbx+13240], rax
	mov rax, QWORD PTR [rbx+29888]
	mov QWORD PTR [rbx+13248], rax
	mov rax, QWORD PTR [rbx+29896]
	mov QWORD PTR [rbx+13256], rax
	mov rax, QWORD PTR [rbx+29904]
	mov QWORD PTR [rbx+13264], rax
	mov rax, QWORD PTR [rbx+29912]
	mov QWORD PTR [rbx+13272], rax
	mov rax, QWORD PTR [rbx+29920]
	mov QWORD PTR [rbx+13280], rax
	mov rax, QWORD PTR [rbx+29928]
	mov QWORD PTR [rbx+13288], rax
	mov rax, QWORD PTR [rbx+29936]
	mov QWORD PTR [rbx+13296], rax
	mov rax, QWORD PTR [rbx+29944]
	mov QWORD PTR [rbx+13304], rax
	mov rax, QWORD PTR [rbx+29952]
	mov QWORD PTR [rbx+13312], rax
	mov rax, QWORD PTR [rbx+29960]
	mov QWORD PTR [rbx+13320], rax
	mov rax, QWORD PTR [rbx+29968]
	mov QWORD PTR [rbx+13328], rax
	mov rax, QWORD PTR [rbx+29976]
	mov QWORD PTR [rbx+13336], rax
	mov rax, QWORD PTR [rbx+29984]
	mov QWORD PTR [rbx+13344], rax
	mov rax, QWORD PTR [rbx+29992]
	mov QWORD PTR [rbx+13352], rax
	mov rax, QWORD PTR [rbx+30000]
	mov QWORD PTR [rbx+13360], rax
	mov rax, QWORD PTR [rbx+30008]
	mov QWORD PTR [rbx+13368], rax
	mov rax, QWORD PTR [rbx+30016]
	mov QWORD PTR [rbx+13376], rax
	mov rax, QWORD PTR [rbx+30024]
	mov QWORD PTR [rbx+13384], rax
	mov rax, QWORD PTR [rbx+30032]
	mov QWORD PTR [rbx+13392], rax
	mov rax, QWORD PTR [rbx+30040]
	mov QWORD PTR [rbx+13400], rax
	mov rax, QWORD PTR [rbx+30048]
	mov QWORD PTR [rbx+13408], rax
	mov rax, QWORD PTR [rbx+30056]
	mov QWORD PTR [rbx+13416], rax
	mov rax, QWORD PTR [rbx+30064]
	mov QWORD PTR [rbx+13424], rax
	mov rax, QWORD PTR [rbx+30072]
	mov QWORD PTR [rbx+13432], rax
	mov rax, QWORD PTR [rbx+30080]
	mov QWORD PTR [rbx+13440], rax
	mov rax, QWORD PTR [rbx+30088]
	mov QWORD PTR [rbx+13448], rax
	mov rax, QWORD PTR [rbx+30096]
	mov QWORD PTR [rbx+13456], rax
	mov rax, QWORD PTR [rbx+30104]
	mov QWORD PTR [rbx+13464], rax
	mov rax, QWORD PTR [rbx+30112]
	mov QWORD PTR [rbx+13472], rax
	mov rax, QWORD PTR [rbx+30120]
	mov QWORD PTR [rbx+13480], rax
	mov rax, QWORD PTR [rbx+30128]
	mov QWORD PTR [rbx+13488], rax
	mov rax, QWORD PTR [rbx+30136]
	mov QWORD PTR [rbx+13496], rax
	mov rax, QWORD PTR [rbx+30144]
	mov QWORD PTR [rbx+13504], rax
	mov rax, QWORD PTR [rbx+30152]
	mov QWORD PTR [rbx+13512], rax
	mov rax, QWORD PTR [rbx+30160]
	mov QWORD PTR [rbx+13520], rax
	mov rax, QWORD PTR [rbx+30168]
	mov QWORD PTR [rbx+13528], rax
	mov rax, QWORD PTR [rbx+30176]
	mov QWORD PTR [rbx+13536], rax
	mov rax, QWORD PTR [rbx+30184]
	mov QWORD PTR [rbx+13544], rax
	mov rax, QWORD PTR [rbx+30192]
	mov QWORD PTR [rbx+13552], rax
	mov rax, QWORD PTR [rbx+30200]
	mov QWORD PTR [rbx+13560], rax
	mov rax, QWORD PTR [rbx+30208]
	mov QWORD PTR [rbx+13568], rax
	mov rax, QWORD PTR [rbx+30216]
	mov QWORD PTR [rbx+13576], rax
	mov rax, QWORD PTR [rbx+30224]
	mov QWORD PTR [rbx+13584], rax
	mov rax, QWORD PTR [rbx+30232]
	mov QWORD PTR [rbx+13592], rax
	mov rax, QWORD PTR [rbx+30240]
	mov QWORD PTR [rbx+13600], rax
	mov rax, QWORD PTR [rbx+30248]
	mov QWORD PTR [rbx+13608], rax
	mov rax, QWORD PTR [rbx+30256]
	mov QWORD PTR [rbx+13616], rax
	mov rax, QWORD PTR [rbx+30264]
	mov QWORD PTR [rbx+13624], rax
	mov rax, QWORD PTR [rbx+30272]
	mov QWORD PTR [rbx+13632], rax
	mov rax, QWORD PTR [rbx+30280]
	mov QWORD PTR [rbx+13640], rax
	mov rax, QWORD PTR [rbx+30288]
	mov QWORD PTR [rbx+13648], rax
	mov rax, QWORD PTR [rbx+30296]
	mov QWORD PTR [rbx+13656], rax
	mov r10, QWORD PTR [rbx+2712]
	add r10, 320
	mov rax, 0
	mov QWORD PTR [rbx+3000], rax
	mov rax, QWORD PTR [rbx+2736]
	mov QWORD PTR [rbx+3008], rax
	mov rax, 3
	mov QWORD PTR [rbx+3016], rax
	mov rax, r12
	mov QWORD PTR [rbx+3024], rax
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 12640
	mov edx, 32
	mov ecx, 9
	mov r8, r10
	mov r9, r13
	call {vg_slhdsa_shake_levels_n32}
	mov rdx, QWORD PTR [rbx+2704]
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+12640]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+12648]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+12656]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+12664]
	mov QWORD PTR [rdx+3896], rax
	mov rax, QWORD PTR [rbx+2712]
	add rax, 480
	mov QWORD PTR [rbx+2712], rax
	mov rax, QWORD PTR [rbx+2736]
	add rax, 16384
	mov QWORD PTR [rbx+2736], rax
	mov rax, QWORD PTR [rbx+2704]
	add rax, 1
	mov QWORD PTR [rbx+2704], rax
	cmp rax, 22
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
	mov edx, 768
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
