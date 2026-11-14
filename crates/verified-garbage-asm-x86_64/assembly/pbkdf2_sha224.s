// The functions of `src/pbkdf2_sha224.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha224_shani:
	lea rsp, [rsp-936]
	mov rax, QWORD PTR [rsp+944]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+144], rbx
	mov QWORD PTR [r8+152], rbp
	mov QWORD PTR [r8+160], r12
	mov QWORD PTR [r8+168], r13
	mov QWORD PTR [r8+176], r14
	mov QWORD PTR [r8+184], r15
	mov r15, r8
	mov QWORD PTR [r15+192], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+200], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 65
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 496
	call {vg_sha224_init_core}
	mov rdi, r15
	add rdi, 496
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rdi, r15
	add rdi, 496
	mov rsi, rbp
	mov rdx, r15
	add rdx, 648
	mov rcx, r15
	call {vg_sha256_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 648
	mov ecx, 28
21:
	mov rdi, r15
	add rdi, 208
	mov rsi, r15
	add rsi, 304
	mov r8, r15
	call {vg_hmac_sha224_init_scratch_shani}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+208]
	mov BYTE PTR [r15+r14*1+400], al
	add r14, 1
	cmp r14, 96
	jne 22b
	mov rdi, r15
	add rdi, 400
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rbp, r13
	mov r13, QWORD PTR [r15+192]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+400]
	mov BYTE PTR [r15+r14*1+496], al
	add r14, 1
	cmp r14, 96
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+680], eax
	mov rdi, r15
	add rdi, 496
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 680
	mov ecx, 4
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rdi, r15
	add rdi, 496
	mov rsi, r15
	add rsi, 304
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 592
	mov r8, r15
	call {vg_hmac_sha224_finalize_scratch_shani}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+592]
	mov BYTE PTR [r15+r14*1+620], al
	add r14, 1
	cmp r14, 28
	jne 27b
	mov rdi, r15
	add rdi, 208
	mov rsi, r15
	add rsi, 592
	mov rdx, QWORD PTR [r15+200]
	mov rcx, r15
	add rcx, 620
	mov r8, r15
	call {vg_pbkdf2_hmac_sha224_iterate_shani}
	mov ecx, 28
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+620]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+936]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-960]
	movdqu XMMWORD PTR [rsp+944], xmm0
	movdqu XMMWORD PTR [rsp+928], xmm0
	movdqu XMMWORD PTR [rsp+912], xmm0
	movdqu XMMWORD PTR [rsp+896], xmm0
	movdqu XMMWORD PTR [rsp+880], xmm0
	movdqu XMMWORD PTR [rsp+864], xmm0
	movdqu XMMWORD PTR [rsp+848], xmm0
	movdqu XMMWORD PTR [rsp+832], xmm0
	movdqu XMMWORD PTR [rsp+816], xmm0
	movdqu XMMWORD PTR [rsp+800], xmm0
	movdqu XMMWORD PTR [rsp+784], xmm0
	movdqu XMMWORD PTR [rsp+768], xmm0
	movdqu XMMWORD PTR [rsp+752], xmm0
	movdqu XMMWORD PTR [rsp+736], xmm0
	movdqu XMMWORD PTR [rsp+720], xmm0
	movdqu XMMWORD PTR [rsp+704], xmm0
	movdqu XMMWORD PTR [rsp+688], xmm0
	movdqu XMMWORD PTR [rsp+672], xmm0
	movdqu XMMWORD PTR [rsp+656], xmm0
	movdqu XMMWORD PTR [rsp+640], xmm0
	movdqu XMMWORD PTR [rsp+624], xmm0
	movdqu XMMWORD PTR [rsp+608], xmm0
	movdqu XMMWORD PTR [rsp+592], xmm0
	movdqu XMMWORD PTR [rsp+576], xmm0
	movdqu XMMWORD PTR [rsp+560], xmm0
	movdqu XMMWORD PTR [rsp+544], xmm0
	movdqu XMMWORD PTR [rsp+528], xmm0
	movdqu XMMWORD PTR [rsp+512], xmm0
	movdqu XMMWORD PTR [rsp+496], xmm0
	movdqu XMMWORD PTR [rsp+480], xmm0
	movdqu XMMWORD PTR [rsp+464], xmm0
	movdqu XMMWORD PTR [rsp+448], xmm0
	movdqu XMMWORD PTR [rsp+432], xmm0
	movdqu XMMWORD PTR [rsp+416], xmm0
	movdqu XMMWORD PTR [rsp+400], xmm0
	movdqu XMMWORD PTR [rsp+384], xmm0
	movdqu XMMWORD PTR [rsp+368], xmm0
	movdqu XMMWORD PTR [rsp+352], xmm0
	movdqu XMMWORD PTR [rsp+336], xmm0
	movdqu XMMWORD PTR [rsp+320], xmm0
	movdqu XMMWORD PTR [rsp+304], xmm0
	movdqu XMMWORD PTR [rsp+288], xmm0
	movdqu XMMWORD PTR [rsp+272], xmm0
	movdqu XMMWORD PTR [rsp+256], xmm0
	movdqu XMMWORD PTR [rsp+240], xmm0
	movdqu XMMWORD PTR [rsp+224], xmm0
	movdqu XMMWORD PTR [rsp+208], xmm0
	movdqu XMMWORD PTR [rsp+192], xmm0
	movdqu XMMWORD PTR [rsp+176], xmm0
	movdqu XMMWORD PTR [rsp+160], xmm0
	movdqu XMMWORD PTR [rsp+144], xmm0
	movdqu XMMWORD PTR [rsp+128], xmm0
	movdqu XMMWORD PTR [rsp+112], xmm0
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+960]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_pbkdf2_hmac_sha224_avx2:
	lea rsp, [rsp-1496]
	mov rax, QWORD PTR [rsp+1504]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+704], rbx
	mov QWORD PTR [r8+712], rbp
	mov QWORD PTR [r8+720], r12
	mov QWORD PTR [r8+728], r13
	mov QWORD PTR [r8+736], r14
	mov QWORD PTR [r8+744], r15
	mov r15, r8
	mov QWORD PTR [r15+752], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+760], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 65
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 1056
	call {vg_sha224_init_core}
	mov rdi, r15
	add rdi, 1056
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rdi, r15
	add rdi, 1056
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1208
	mov rcx, r15
	call {vg_sha256_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 1208
	mov ecx, 28
21:
	mov rdi, r15
	add rdi, 768
	mov rsi, r15
	add rsi, 864
	mov r8, r15
	call {vg_hmac_sha224_init_scratch_avx2}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+768]
	mov BYTE PTR [r15+r14*1+960], al
	add r14, 1
	cmp r14, 96
	jne 22b
	mov rdi, r15
	add rdi, 960
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rbp, r13
	mov r13, QWORD PTR [r15+752]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+960]
	mov BYTE PTR [r15+r14*1+1056], al
	add r14, 1
	cmp r14, 96
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+1240], eax
	mov rdi, r15
	add rdi, 1056
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 1240
	mov ecx, 4
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rdi, r15
	add rdi, 1056
	mov rsi, r15
	add rsi, 864
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 1152
	mov r8, r15
	call {vg_hmac_sha224_finalize_scratch_avx2}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+1152]
	mov BYTE PTR [r15+r14*1+1180], al
	add r14, 1
	cmp r14, 28
	jne 27b
	mov rdi, r15
	add rdi, 768
	mov rsi, r15
	add rsi, 1152
	mov rdx, QWORD PTR [r15+760]
	mov rcx, r15
	add rcx, 1180
	mov r8, r15
	call {vg_pbkdf2_hmac_sha224_iterate_avx2}
	mov ecx, 28
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+1180]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+704]
	mov rbp, QWORD PTR [r15+712]
	mov r12, QWORD PTR [r15+720]
	mov r13, QWORD PTR [r15+728]
	mov r14, QWORD PTR [r15+736]
	mov r15, QWORD PTR [r15+744]
	lea rsp, [rsp+1496]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-1520]
	vmovdqu YMMWORD PTR [rsp+1488], ymm0
	vmovdqu YMMWORD PTR [rsp+1456], ymm0
	vmovdqu YMMWORD PTR [rsp+1424], ymm0
	vmovdqu YMMWORD PTR [rsp+1392], ymm0
	vmovdqu YMMWORD PTR [rsp+1360], ymm0
	vmovdqu YMMWORD PTR [rsp+1328], ymm0
	vmovdqu YMMWORD PTR [rsp+1296], ymm0
	vmovdqu YMMWORD PTR [rsp+1264], ymm0
	vmovdqu YMMWORD PTR [rsp+1232], ymm0
	vmovdqu YMMWORD PTR [rsp+1200], ymm0
	vmovdqu YMMWORD PTR [rsp+1168], ymm0
	vmovdqu YMMWORD PTR [rsp+1136], ymm0
	vmovdqu YMMWORD PTR [rsp+1104], ymm0
	vmovdqu YMMWORD PTR [rsp+1072], ymm0
	vmovdqu YMMWORD PTR [rsp+1040], ymm0
	vmovdqu YMMWORD PTR [rsp+1008], ymm0
	vmovdqu YMMWORD PTR [rsp+976], ymm0
	vmovdqu YMMWORD PTR [rsp+944], ymm0
	vmovdqu YMMWORD PTR [rsp+912], ymm0
	vmovdqu YMMWORD PTR [rsp+880], ymm0
	vmovdqu YMMWORD PTR [rsp+848], ymm0
	vmovdqu YMMWORD PTR [rsp+816], ymm0
	vmovdqu YMMWORD PTR [rsp+784], ymm0
	vmovdqu YMMWORD PTR [rsp+752], ymm0
	vmovdqu YMMWORD PTR [rsp+720], ymm0
	vmovdqu YMMWORD PTR [rsp+688], ymm0
	vmovdqu YMMWORD PTR [rsp+656], ymm0
	vmovdqu YMMWORD PTR [rsp+624], ymm0
	vmovdqu YMMWORD PTR [rsp+592], ymm0
	vmovdqu YMMWORD PTR [rsp+560], ymm0
	vmovdqu YMMWORD PTR [rsp+528], ymm0
	vmovdqu YMMWORD PTR [rsp+496], ymm0
	vmovdqu YMMWORD PTR [rsp+464], ymm0
	vmovdqu YMMWORD PTR [rsp+432], ymm0
	vmovdqu YMMWORD PTR [rsp+400], ymm0
	vmovdqu YMMWORD PTR [rsp+368], ymm0
	vmovdqu YMMWORD PTR [rsp+336], ymm0
	vmovdqu YMMWORD PTR [rsp+304], ymm0
	vmovdqu YMMWORD PTR [rsp+272], ymm0
	vmovdqu YMMWORD PTR [rsp+240], ymm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+1520]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_pbkdf2_hmac_sha224:
	lea rsp, [rsp-1048]
	mov rax, QWORD PTR [rsp+1056]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+256], rbx
	mov QWORD PTR [r8+264], rbp
	mov QWORD PTR [r8+272], r12
	mov QWORD PTR [r8+280], r13
	mov QWORD PTR [r8+288], r14
	mov QWORD PTR [r8+296], r15
	mov r15, r8
	mov QWORD PTR [r15+304], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+312], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 65
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 608
	call {vg_sha224_init_core}
	mov rdi, r15
	add rdi, 608
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch}
	mov rdi, r15
	add rdi, 608
	mov rsi, rbp
	mov rdx, r15
	add rdx, 760
	mov rcx, r15
	call {vg_sha256_finalize_scratch}
	mov rdx, r15
	add rdx, 760
	mov ecx, 28
21:
	mov rdi, r15
	add rdi, 320
	mov rsi, r15
	add rsi, 416
	mov r8, r15
	call {vg_hmac_sha224_init_scratch}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+320]
	mov BYTE PTR [r15+r14*1+512], al
	add r14, 1
	cmp r14, 96
	jne 22b
	mov rdi, r15
	add rdi, 512
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha256_update_scratch}
	mov rbp, r13
	mov r13, QWORD PTR [r15+304]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+512]
	mov BYTE PTR [r15+r14*1+608], al
	add r14, 1
	cmp r14, 96
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+792], eax
	mov rdi, r15
	add rdi, 608
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 792
	mov ecx, 4
	mov r8, r15
	call {vg_sha256_update_scratch}
	mov rdi, r15
	add rdi, 608
	mov rsi, r15
	add rsi, 416
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 704
	mov r8, r15
	call {vg_hmac_sha224_finalize_scratch}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+704]
	mov BYTE PTR [r15+r14*1+732], al
	add r14, 1
	cmp r14, 28
	jne 27b
	mov rdi, r15
	add rdi, 320
	mov rsi, r15
	add rsi, 704
	mov rdx, QWORD PTR [r15+312]
	mov rcx, r15
	add rcx, 732
	mov r8, r15
	call {vg_pbkdf2_hmac_sha224_iterate}
	mov ecx, 28
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+732]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+256]
	mov rbp, QWORD PTR [r15+264]
	mov r12, QWORD PTR [r15+272]
	mov r13, QWORD PTR [r15+280]
	mov r14, QWORD PTR [r15+288]
	mov r15, QWORD PTR [r15+296]
	lea rsp, [rsp+1048]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-1072]
	movdqu XMMWORD PTR [rsp+1056], xmm0
	movdqu XMMWORD PTR [rsp+1040], xmm0
	movdqu XMMWORD PTR [rsp+1024], xmm0
	movdqu XMMWORD PTR [rsp+1008], xmm0
	movdqu XMMWORD PTR [rsp+992], xmm0
	movdqu XMMWORD PTR [rsp+976], xmm0
	movdqu XMMWORD PTR [rsp+960], xmm0
	movdqu XMMWORD PTR [rsp+944], xmm0
	movdqu XMMWORD PTR [rsp+928], xmm0
	movdqu XMMWORD PTR [rsp+912], xmm0
	movdqu XMMWORD PTR [rsp+896], xmm0
	movdqu XMMWORD PTR [rsp+880], xmm0
	movdqu XMMWORD PTR [rsp+864], xmm0
	movdqu XMMWORD PTR [rsp+848], xmm0
	movdqu XMMWORD PTR [rsp+832], xmm0
	movdqu XMMWORD PTR [rsp+816], xmm0
	movdqu XMMWORD PTR [rsp+800], xmm0
	movdqu XMMWORD PTR [rsp+784], xmm0
	movdqu XMMWORD PTR [rsp+768], xmm0
	movdqu XMMWORD PTR [rsp+752], xmm0
	movdqu XMMWORD PTR [rsp+736], xmm0
	movdqu XMMWORD PTR [rsp+720], xmm0
	movdqu XMMWORD PTR [rsp+704], xmm0
	movdqu XMMWORD PTR [rsp+688], xmm0
	movdqu XMMWORD PTR [rsp+672], xmm0
	movdqu XMMWORD PTR [rsp+656], xmm0
	movdqu XMMWORD PTR [rsp+640], xmm0
	movdqu XMMWORD PTR [rsp+624], xmm0
	movdqu XMMWORD PTR [rsp+608], xmm0
	movdqu XMMWORD PTR [rsp+592], xmm0
	movdqu XMMWORD PTR [rsp+576], xmm0
	movdqu XMMWORD PTR [rsp+560], xmm0
	movdqu XMMWORD PTR [rsp+544], xmm0
	movdqu XMMWORD PTR [rsp+528], xmm0
	movdqu XMMWORD PTR [rsp+512], xmm0
	movdqu XMMWORD PTR [rsp+496], xmm0
	movdqu XMMWORD PTR [rsp+480], xmm0
	movdqu XMMWORD PTR [rsp+464], xmm0
	movdqu XMMWORD PTR [rsp+448], xmm0
	movdqu XMMWORD PTR [rsp+432], xmm0
	movdqu XMMWORD PTR [rsp+416], xmm0
	movdqu XMMWORD PTR [rsp+400], xmm0
	movdqu XMMWORD PTR [rsp+384], xmm0
	movdqu XMMWORD PTR [rsp+368], xmm0
	movdqu XMMWORD PTR [rsp+352], xmm0
	movdqu XMMWORD PTR [rsp+336], xmm0
	movdqu XMMWORD PTR [rsp+320], xmm0
	movdqu XMMWORD PTR [rsp+304], xmm0
	movdqu XMMWORD PTR [rsp+288], xmm0
	movdqu XMMWORD PTR [rsp+272], xmm0
	movdqu XMMWORD PTR [rsp+256], xmm0
	movdqu XMMWORD PTR [rsp+240], xmm0
	movdqu XMMWORD PTR [rsp+224], xmm0
	movdqu XMMWORD PTR [rsp+208], xmm0
	movdqu XMMWORD PTR [rsp+192], xmm0
	movdqu XMMWORD PTR [rsp+176], xmm0
	movdqu XMMWORD PTR [rsp+160], xmm0
	movdqu XMMWORD PTR [rsp+144], xmm0
	movdqu XMMWORD PTR [rsp+128], xmm0
	movdqu XMMWORD PTR [rsp+112], xmm0
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+1072]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6
