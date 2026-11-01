// The functions of `src/mlkem.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_add:
	mov eax, 3329
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov ecx, 64
20:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu xmm1, XMMWORD PTR [rsi]
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm1, xmm0
	psrad xmm1, 31
	pand xmm1, xmm15
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rsi, 16
	sub rcx, 1
	jne 20b
	ret
	.p2align 6

vg_mlkem_sub:
	mov eax, 3329
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov ecx, 64
20:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu xmm1, XMMWORD PTR [rsi]
	psubd xmm0, xmm1
	movdqa xmm1, xmm0
	psrad xmm1, 31
	pand xmm1, xmm15
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rsi, 16
	sub rcx, 1
	jne 20b
	ret
	.p2align 6

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

vg_mlkem_encode12:
	mov ecx, 128
20:
	mov eax, DWORD PTR [rdi]
	mov edx, DWORD PTR [rdi+4]
	ror edx, 20
	add eax, edx
	mov BYTE PTR [rsi], al
	shr eax, 8
	mov BYTE PTR [rsi+1], al
	shr eax, 8
	mov BYTE PTR [rsi+2], al
	add rdi, 8
	add rsi, 3
	sub rcx, 1
	jne 20b
	ret
	.p2align 6

vg_mlkem_decode12:
	mov ecx, 128
20:
	movzx eax, BYTE PTR [rdi]
	movzx edx, BYTE PTR [rdi+1]
	ror edx, 24
	add eax, edx
	movzx edx, BYTE PTR [rdi+2]
	ror edx, 16
	add eax, edx
	mov edx, eax
	and eax, 4095
	shr edx, 12
	sub eax, 3329
	sbb r8d, r8d
	and r8d, 3329
	add eax, r8d
	sub edx, 3329
	sbb r8d, r8d
	and r8d, 3329
	add edx, r8d
	mov DWORD PTR [rsi], eax
	mov DWORD PTR [rsi+4], edx
	add rdi, 3
	add rsi, 8
	sub rcx, 1
	jne 20b
	ret
	.p2align 6

vg_mlkem_cbd2:
	mov eax, 3329
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov eax, 16711935
	movq xmm8, rax
	pshufd xmm8, xmm8, 0
	mov eax, 5570645
	movq xmm9, rax
	pshufd xmm9, xmm9, 0
	mov eax, 3342387
	movq xmm10, rax
	pshufd xmm10, xmm10, 0
	mov eax, 2228258
	movq xmm11, rax
	pshufd xmm11, xmm11, 0
	mov eax, 983055
	movq xmm12, rax
	pshufd xmm12, xmm12, 0
	mov eax, 2
	movq xmm13, rax
	pshufd xmm13, xmm13, 0
	pxor xmm14, xmm14
	mov ecx, 8
20:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqa xmm1, xmm0
	psrlw xmm1, 8
	pand xmm0, xmm8
	movdqa xmm2, xmm0
	psrlw xmm2, 1
	pand xmm2, xmm9
	pand xmm0, xmm9
	paddw xmm0, xmm2
	movdqa xmm2, xmm0
	psrlw xmm2, 2
	pand xmm2, xmm10
	pand xmm0, xmm10
	paddw xmm0, xmm11
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psrlw xmm2, 4
	pand xmm0, xmm12
	movdqa xmm3, xmm1
	psrlw xmm3, 1
	pand xmm3, xmm9
	pand xmm1, xmm9
	paddw xmm1, xmm3
	movdqa xmm3, xmm1
	psrlw xmm3, 2
	pand xmm3, xmm10
	pand xmm1, xmm10
	paddw xmm1, xmm11
	psubw xmm1, xmm3
	movdqa xmm3, xmm1
	psrlw xmm3, 4
	pand xmm1, xmm12
	movdqa xmm4, xmm0
	punpcklwd xmm4, xmm2
	punpckhwd xmm0, xmm2
	movdqa xmm2, xmm1
	punpcklwd xmm2, xmm3
	punpckhwd xmm1, xmm3
	movdqa xmm5, xmm4
	punpcklwd xmm5, xmm14
	movdqa xmm6, xmm2
	punpcklwd xmm6, xmm14
	movdqa xmm7, xmm5
	punpcklqdq xmm7, xmm6
	punpckhqdq xmm5, xmm6
	psubd xmm7, xmm13
	movdqa xmm6, xmm7
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm7, xmm6
	movdqu XMMWORD PTR [rsi], xmm7
	psubd xmm5, xmm13
	movdqa xmm6, xmm5
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm5, xmm6
	movdqu XMMWORD PTR [rsi+16], xmm5
	punpckhwd xmm4, xmm14
	punpckhwd xmm2, xmm14
	movdqa xmm7, xmm4
	punpcklqdq xmm7, xmm2
	punpckhqdq xmm4, xmm2
	psubd xmm7, xmm13
	movdqa xmm6, xmm7
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm7, xmm6
	movdqu XMMWORD PTR [rsi+32], xmm7
	psubd xmm4, xmm13
	movdqa xmm6, xmm4
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm4, xmm6
	movdqu XMMWORD PTR [rsi+48], xmm4
	movdqa xmm5, xmm0
	punpcklwd xmm5, xmm14
	movdqa xmm6, xmm1
	punpcklwd xmm6, xmm14
	movdqa xmm7, xmm5
	punpcklqdq xmm7, xmm6
	punpckhqdq xmm5, xmm6
	psubd xmm7, xmm13
	movdqa xmm6, xmm7
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm7, xmm6
	movdqu XMMWORD PTR [rsi+64], xmm7
	psubd xmm5, xmm13
	movdqa xmm6, xmm5
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm5, xmm6
	movdqu XMMWORD PTR [rsi+80], xmm5
	punpckhwd xmm0, xmm14
	punpckhwd xmm1, xmm14
	movdqa xmm7, xmm0
	punpcklqdq xmm7, xmm1
	punpckhqdq xmm0, xmm1
	psubd xmm7, xmm13
	movdqa xmm6, xmm7
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm7, xmm6
	movdqu XMMWORD PTR [rsi+96], xmm7
	psubd xmm0, xmm13
	movdqa xmm6, xmm0
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm0, xmm6
	movdqu XMMWORD PTR [rsi+112], xmm0
	add rdi, 16
	add rsi, 128
	sub rcx, 1
	jne 20b
	ret
	.p2align 6

vg_mlkem_compress_encode:
	mov esi, esi
	mov r8, rdx
	cmp esi, 1
	je 20f
	cmp esi, 4
	je 22f
	mov r9, 161271
	mov ecx, 64
24:
	mov r10d, 0
	mov eax, DWORD PTR [rdi+12]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1023
	ror r10, 54
	add r10, rax
	mov eax, DWORD PTR [rdi+8]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1023
	ror r10, 54
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1023
	ror r10, 54
	add r10, rax
	mov eax, DWORD PTR [rdi]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1023
	ror r10, 54
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	mov BYTE PTR [r8+3], r10b
	shr r10, 8
	mov BYTE PTR [r8+4], r10b
	shr r10, 8
	add rdi, 16
	add r8, 5
	sub rcx, 1
	jne 24b
	jmp 23f
22:
	mov r9, 2520
	mov ecx, 128
25:
	mov r10d, 0
	mov eax, DWORD PTR [rdi+4]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 15
	ror r10, 60
	add r10, rax
	mov eax, DWORD PTR [rdi]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 15
	ror r10, 60
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	add rdi, 8
	add r8, 1
	sub rcx, 1
	jne 25b
23:
	jmp 21f
20:
	mov r9, 315
	mov ecx, 32
26:
	mov r10d, 0
	mov eax, DWORD PTR [rdi+28]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+24]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+20]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+16]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+12]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+8]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	add rdi, 32
	add r8, 1
	sub rcx, 1
	jne 26b
21:
	ret
	.p2align 6

vg_mlkem_decode_decompress:
	mov edx, edx
	mov rsi, rcx
	cmp edx, 1
	je 20f
	cmp edx, 4
	je 22f
	mov r9, 3329
	mov ecx, 64
24:
	mov r10d, 0
	movzx eax, BYTE PTR [rdi+4]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+3]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+2]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+1]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi]
	ror r10, 56
	add r10, rax
	mov rax, r10
	and eax, 1023
	mul r9
	add rax, 512
	shr rax, 10
	mov DWORD PTR [rsi], eax
	shr r10, 10
	mov rax, r10
	and eax, 1023
	mul r9
	add rax, 512
	shr rax, 10
	mov DWORD PTR [rsi+4], eax
	shr r10, 10
	mov rax, r10
	and eax, 1023
	mul r9
	add rax, 512
	shr rax, 10
	mov DWORD PTR [rsi+8], eax
	shr r10, 10
	mov rax, r10
	and eax, 1023
	mul r9
	add rax, 512
	shr rax, 10
	mov DWORD PTR [rsi+12], eax
	shr r10, 10
	add rdi, 5
	add rsi, 16
	sub rcx, 1
	jne 24b
	jmp 23f
22:
	mov r9, 3329
	mov ecx, 128
25:
	mov r10d, 0
	movzx eax, BYTE PTR [rdi]
	ror r10, 56
	add r10, rax
	mov rax, r10
	and eax, 15
	mul r9
	add rax, 8
	shr rax, 4
	mov DWORD PTR [rsi], eax
	shr r10, 4
	mov rax, r10
	and eax, 15
	mul r9
	add rax, 8
	shr rax, 4
	mov DWORD PTR [rsi+4], eax
	shr r10, 4
	add rdi, 1
	add rsi, 8
	sub rcx, 1
	jne 25b
23:
	jmp 21f
20:
	mov r9, 3329
	mov ecx, 32
26:
	mov r10d, 0
	movzx eax, BYTE PTR [rdi]
	ror r10, 56
	add r10, rax
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+4], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+8], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+12], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+16], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+20], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+24], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+28], eax
	shr r10, 1
	add rdi, 1
	add rsi, 32
	sub rcx, 1
	jne 26b
21:
	ret
	.p2align 6

vg_mlkem_sample_ntt4:
	mov QWORD PTR [rdx+4384], rbx
	mov QWORD PTR [rdx+4392], rbp
	mov QWORD PTR [rdx+4400], r12
	mov QWORD PTR [rdx+4408], r13
	mov QWORD PTR [rdx+4416], r14
	mov rbx, rdx
	mov r12, rdi
	mov r13, rsi
	mov r14d, 1
	mov rdi, r12
	add rdi, 0
	mov rsi, r13
	add rsi, 0
	mov rdx, rbx
	add rdx, 6144
	call {vg_mlkem_sample_ntt}
	and r14d, eax
	mov rdi, r12
	add rdi, 34
	mov rsi, r13
	add rsi, 1024
	mov rdx, rbx
	add rdx, 6144
	call {vg_mlkem_sample_ntt}
	and r14d, eax
	mov rdi, r12
	add rdi, 68
	mov rsi, r13
	add rsi, 2048
	mov rdx, rbx
	add rdx, 6144
	call {vg_mlkem_sample_ntt}
	and r14d, eax
	mov rdi, r12
	add rdi, 102
	mov rsi, r13
	add rsi, 3072
	mov rdx, rbx
	add rdx, 6144
	call {vg_mlkem_sample_ntt}
	and r14d, eax
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	ret
	.p2align 6
