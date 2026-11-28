// The functions of `src/internal/vg_slhdsa_shake_fors_128s_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_fors_128s_avx2:
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
	shr rax, 12
	and rax, 4095
	mov QWORD PTR [rbx+31328], rax
	movzx eax, BYTE PTR [rbp+1]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+2]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+3]
	or rax, rcx
	shr rax, 8
	and rax, 4095
	mov QWORD PTR [rbx+31336], rax
	movzx eax, BYTE PTR [rbp+3]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+4]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+5]
	or rax, rcx
	shr rax, 12
	and rax, 4095
	mov QWORD PTR [rbx+31344], rax
	movzx eax, BYTE PTR [rbp+4]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+5]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+6]
	or rax, rcx
	shr rax, 8
	and rax, 4095
	mov QWORD PTR [rbx+31352], rax
	movzx eax, BYTE PTR [rbp+6]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+7]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+8]
	or rax, rcx
	shr rax, 12
	and rax, 4095
	mov QWORD PTR [rbx+31360], rax
	movzx eax, BYTE PTR [rbp+7]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+8]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+9]
	or rax, rcx
	shr rax, 8
	and rax, 4095
	mov QWORD PTR [rbx+31368], rax
	movzx eax, BYTE PTR [rbp+9]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+10]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+11]
	or rax, rcx
	shr rax, 12
	and rax, 4095
	mov QWORD PTR [rbx+31376], rax
	movzx eax, BYTE PTR [rbp+10]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+11]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+12]
	or rax, rcx
	shr rax, 8
	and rax, 4095
	mov QWORD PTR [rbx+31384], rax
	movzx eax, BYTE PTR [rbp+12]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+13]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+14]
	or rax, rcx
	shr rax, 12
	and rax, 4095
	mov QWORD PTR [rbx+31392], rax
	movzx eax, BYTE PTR [rbp+13]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+14]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+15]
	or rax, rcx
	shr rax, 8
	and rax, 4095
	mov QWORD PTR [rbx+31400], rax
	movzx eax, BYTE PTR [rbp+15]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+16]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+17]
	or rax, rcx
	shr rax, 12
	and rax, 4095
	mov QWORD PTR [rbx+31408], rax
	movzx eax, BYTE PTR [rbp+16]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+17]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+18]
	or rax, rcx
	shr rax, 8
	and rax, 4095
	mov QWORD PTR [rbx+31416], rax
	movzx eax, BYTE PTR [rbp+18]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+19]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+20]
	or rax, rcx
	shr rax, 12
	and rax, 4095
	mov QWORD PTR [rbx+31424], rax
	movzx eax, BYTE PTR [rbp+19]
	shl rax, 16
	movzx ecx, BYTE PTR [rbp+20]
	shl rcx, 8
	or rax, rcx
	movzx ecx, BYTE PTR [rbp+21]
	or rax, rcx
	shr rax, 8
	and rax, 4095
	mov QWORD PTR [rbx+31432], rax
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
	mov DWORD PTR [rbx+3328], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3332], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3336], eax
	mov r11, r10
	add r11, 0
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3340], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3344], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3352], rax
	mov eax, 6
	bswap eax
	mov DWORD PTR [rbx+3456], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3460], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3464], eax
	mov r11, r10
	add r11, 1
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3468], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3472], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3480], rax
	mov eax, 6
	bswap eax
	mov DWORD PTR [rbx+3584], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3588], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3592], eax
	mov r11, r10
	add r11, 2
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3596], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3600], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3608], rax
	mov eax, 6
	bswap eax
	mov DWORD PTR [rbx+3712], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3716], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3720], eax
	mov r11, r10
	add r11, 3
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3724], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3728], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3736], rax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 64
	mov rcx, rdi
	add rcx, 48
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n16_avx2}
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
	mov rax, QWORD PTR [rbx+3344]
	and rax, rdi
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rbx+3352]
	and rax, rdi
	xor rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsi+8], rax
	mov rax, rdx
	add rax, 1
	xor rax, r13
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rbx+3472]
	and rax, rdi
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rbx+3480]
	and rax, rdi
	xor rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsi+8], rax
	mov rax, rdx
	add rax, 2
	xor rax, r13
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rbx+3600]
	and rax, rdi
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rbx+3608]
	and rax, rdi
	xor rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsi+8], rax
	mov rax, rdx
	add rax, 3
	xor rax, r13
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rbx+3728]
	and rax, rdi
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rbx+3736]
	and rax, rdi
	xor rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsi+8], rax
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3328], eax
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3456], eax
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3584], eax
	mov eax, 3
	bswap eax
	mov DWORD PTR [rbx+3712], eax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 64
	mov rcx, rdi
	add rcx, 48
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n16_avx2}
	mov rdx, QWORD PTR [rbx+2728]
	shl rdx, 4
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3344]
	mov QWORD PTR [rdx+12640], rax
	mov rax, QWORD PTR [rbx+3352]
	mov QWORD PTR [rdx+12648], rax
	mov rax, QWORD PTR [rbx+3472]
	mov QWORD PTR [rdx+12656], rax
	mov rax, QWORD PTR [rbx+3480]
	mov QWORD PTR [rdx+12664], rax
	mov rax, QWORD PTR [rbx+3600]
	mov QWORD PTR [rdx+12672], rax
	mov rax, QWORD PTR [rbx+3608]
	mov QWORD PTR [rdx+12680], rax
	mov rax, QWORD PTR [rbx+3728]
	mov QWORD PTR [rdx+12688], rax
	mov rax, QWORD PTR [rbx+3736]
	mov QWORD PTR [rdx+12696], rax
	mov rax, QWORD PTR [rbx+2728]
	add rax, 4
	mov QWORD PTR [rbx+2728], rax
	cmp rax, 512
	jb 22b
	mov r10, QWORD PTR [rbx+2712]
	add r10, 16
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
	call {vg_slhdsa_shake_levels_n16_avx2}
	mov rdx, QWORD PTR [rbx+2720]
	shr rdx, 9
	shl rdx, 4
	add rdx, rbx
	mov rax, QWORD PTR [rbx+12640]
	mov QWORD PTR [rdx+29280], rax
	mov rax, QWORD PTR [rbx+12648]
	mov QWORD PTR [rdx+29288], rax
	mov rax, QWORD PTR [rbx+2720]
	add rax, 512
	mov QWORD PTR [rbx+2720], rax
	cmp rax, 4096
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
	mov r10, QWORD PTR [rbx+2712]
	add r10, 160
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
	mov edx, 8
	mov ecx, 9
	mov r8, r10
	mov r9, r13
	call {vg_slhdsa_shake_levels_n16_avx2}
	mov rdx, QWORD PTR [rbx+2704]
	shl rdx, 4
	add rdx, rbx
	mov rax, QWORD PTR [rbx+12640]
	mov QWORD PTR [rdx+3856], rax
	mov rax, QWORD PTR [rbx+12648]
	mov QWORD PTR [rdx+3864], rax
	mov rax, QWORD PTR [rbx+2712]
	add rax, 208
	mov QWORD PTR [rbx+2712], rax
	mov rax, QWORD PTR [rbx+2736]
	add rax, 4096
	mov QWORD PTR [rbx+2736], rax
	mov rax, QWORD PTR [rbx+2704]
	add rax, 1
	mov QWORD PTR [rbx+2704], rax
	cmp rax, 14
	jne 20b
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
	mov edx, 272
	mov rcx, rdi
	add rcx, 48
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n16_avx2}
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
