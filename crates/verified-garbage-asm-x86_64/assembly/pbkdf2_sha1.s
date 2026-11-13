// The functions of `src/pbkdf2_sha1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1_shani:
	lea rsp, [rsp-832]
	mov rax, QWORD PTR [rsp+840]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+136], rbx
	mov QWORD PTR [r8+144], rbp
	mov QWORD PTR [r8+152], r12
	mov QWORD PTR [r8+160], r13
	mov QWORD PTR [r8+168], r14
	mov QWORD PTR [r8+176], r15
	mov r15, r8
	mov QWORD PTR [r15+184], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+192], rax
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
	add rdi, 452
	call {vg_sha1_init_core}
	mov rdi, r15
	add rdi, 452
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha1_update_scratch_shani}
	mov rdi, r15
	add rdi, 452
	mov rsi, rbp
	mov rdx, r15
	add rdx, 576
	mov rcx, r15
	call {vg_sha1_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 576
	mov ecx, 20
21:
	mov rdi, r15
	add rdi, 200
	mov rsi, r15
	add rsi, 284
	mov r8, r15
	call {vg_hmac_sha1_init_scratch_shani}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+200]
	mov BYTE PTR [r15+r14*1+368], al
	add r14, 1
	cmp r14, 84
	jne 22b
	mov rdi, r15
	add rdi, 368
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha1_update_scratch_shani}
	mov rbp, r13
	mov r13, QWORD PTR [r15+184]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+368]
	mov BYTE PTR [r15+r14*1+452], al
	add r14, 1
	cmp r14, 84
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+596], eax
	mov rdi, r15
	add rdi, 452
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 596
	mov ecx, 4
	mov r8, r15
	call {vg_sha1_update_scratch_shani}
	mov rdi, r15
	add rdi, 452
	mov rsi, r15
	add rsi, 284
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 536
	mov r8, r15
	call {vg_hmac_sha1_finalize_scratch_shani}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+536]
	mov BYTE PTR [r15+r14*1+556], al
	add r14, 1
	cmp r14, 20
	jne 27b
	mov rdi, r15
	add rdi, 200
	mov rsi, r15
	add rsi, 536
	mov rdx, QWORD PTR [r15+192]
	mov rcx, r15
	add rcx, 556
	mov r8, r15
	call {vg_pbkdf2_hmac_sha1_iterate_shani}
	mov ecx, 20
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+556]
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
	mov rbx, QWORD PTR [r15+136]
	mov rbp, QWORD PTR [r15+144]
	mov r12, QWORD PTR [r15+152]
	mov r13, QWORD PTR [r15+160]
	mov r14, QWORD PTR [r15+168]
	mov r15, QWORD PTR [r15+176]
	lea rsp, [rsp+832]
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
	lea rsp, [rsp-856]
	mov QWORD PTR [rsp+848], r11
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
	lea rsp, [rsp+856]
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

vg_pbkdf2_hmac_sha1_avx_bmi:
	lea rsp, [rsp-944]
	mov rax, QWORD PTR [rsp+952]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+248], rbx
	mov QWORD PTR [r8+256], rbp
	mov QWORD PTR [r8+264], r12
	mov QWORD PTR [r8+272], r13
	mov QWORD PTR [r8+280], r14
	mov QWORD PTR [r8+288], r15
	mov r15, r8
	mov QWORD PTR [r15+296], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+304], rax
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
	add rdi, 564
	call {vg_sha1_init_core}
	mov rdi, r15
	add rdi, 564
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha1_update_scratch_avx_bmi}
	mov rdi, r15
	add rdi, 564
	mov rsi, rbp
	mov rdx, r15
	add rdx, 688
	mov rcx, r15
	call {vg_sha1_finalize_scratch_avx_bmi}
	mov rdx, r15
	add rdx, 688
	mov ecx, 20
21:
	mov rdi, r15
	add rdi, 312
	mov rsi, r15
	add rsi, 396
	mov r8, r15
	call {vg_hmac_sha1_init_scratch_avx_bmi}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+312]
	mov BYTE PTR [r15+r14*1+480], al
	add r14, 1
	cmp r14, 84
	jne 22b
	mov rdi, r15
	add rdi, 480
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha1_update_scratch_avx_bmi}
	mov rbp, r13
	mov r13, QWORD PTR [r15+296]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+480]
	mov BYTE PTR [r15+r14*1+564], al
	add r14, 1
	cmp r14, 84
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+708], eax
	mov rdi, r15
	add rdi, 564
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 708
	mov ecx, 4
	mov r8, r15
	call {vg_sha1_update_scratch_avx_bmi}
	mov rdi, r15
	add rdi, 564
	mov rsi, r15
	add rsi, 396
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 648
	mov r8, r15
	call {vg_hmac_sha1_finalize_scratch_avx_bmi}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+648]
	mov BYTE PTR [r15+r14*1+668], al
	add r14, 1
	cmp r14, 20
	jne 27b
	mov rdi, r15
	add rdi, 312
	mov rsi, r15
	add rsi, 648
	mov rdx, QWORD PTR [r15+304]
	mov rcx, r15
	add rcx, 668
	mov r8, r15
	call {vg_pbkdf2_hmac_sha1_iterate_avx_bmi}
	mov ecx, 20
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+668]
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
	mov rbx, QWORD PTR [r15+248]
	mov rbp, QWORD PTR [r15+256]
	mov r12, QWORD PTR [r15+264]
	mov r13, QWORD PTR [r15+272]
	mov r14, QWORD PTR [r15+280]
	mov r15, QWORD PTR [r15+288]
	lea rsp, [rsp+944]
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
	mov r11d, 16
	test r11d, esp
	je 211f
	xor r11d, r11d
	lea rsp, [rsp-968]
	mov QWORD PTR [rsp+960], r11
	movdqu XMMWORD PTR [rsp+944], xmm0
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
	lea rsp, [rsp+968]
	jmp 212f
211:
	xor r11d, r11d
	lea rsp, [rsp-968]
	mov QWORD PTR [rsp+960], r11
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+968]
212:
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

vg_pbkdf2_hmac_sha1:
	lea rsp, [rsp-944]
	mov rax, QWORD PTR [rsp+952]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+248], rbx
	mov QWORD PTR [r8+256], rbp
	mov QWORD PTR [r8+264], r12
	mov QWORD PTR [r8+272], r13
	mov QWORD PTR [r8+280], r14
	mov QWORD PTR [r8+288], r15
	mov r15, r8
	mov QWORD PTR [r15+296], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+304], rax
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
	add rdi, 564
	call {vg_sha1_init_core}
	mov rdi, r15
	add rdi, 564
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha1_update_scratch}
	mov rdi, r15
	add rdi, 564
	mov rsi, rbp
	mov rdx, r15
	add rdx, 688
	mov rcx, r15
	call {vg_sha1_finalize_scratch}
	mov rdx, r15
	add rdx, 688
	mov ecx, 20
21:
	mov rdi, r15
	add rdi, 312
	mov rsi, r15
	add rsi, 396
	mov r8, r15
	call {vg_hmac_sha1_init_scratch}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+312]
	mov BYTE PTR [r15+r14*1+480], al
	add r14, 1
	cmp r14, 84
	jne 22b
	mov rdi, r15
	add rdi, 480
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha1_update_scratch}
	mov rbp, r13
	mov r13, QWORD PTR [r15+296]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+480]
	mov BYTE PTR [r15+r14*1+564], al
	add r14, 1
	cmp r14, 84
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+708], eax
	mov rdi, r15
	add rdi, 564
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 708
	mov ecx, 4
	mov r8, r15
	call {vg_sha1_update_scratch}
	mov rdi, r15
	add rdi, 564
	mov rsi, r15
	add rsi, 396
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 648
	mov r8, r15
	call {vg_hmac_sha1_finalize_scratch}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+648]
	mov BYTE PTR [r15+r14*1+668], al
	add r14, 1
	cmp r14, 20
	jne 27b
	mov rdi, r15
	add rdi, 312
	mov rsi, r15
	add rsi, 648
	mov rdx, QWORD PTR [r15+304]
	mov rcx, r15
	add rcx, 668
	mov r8, r15
	call {vg_pbkdf2_hmac_sha1_iterate}
	mov ecx, 20
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+668]
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
	mov rbx, QWORD PTR [r15+248]
	mov rbp, QWORD PTR [r15+256]
	mov r12, QWORD PTR [r15+264]
	mov r13, QWORD PTR [r15+272]
	mov r14, QWORD PTR [r15+280]
	mov r15, QWORD PTR [r15+288]
	lea rsp, [rsp+944]
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
	lea rsp, [rsp-968]
	mov QWORD PTR [rsp+960], r11
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
	lea rsp, [rsp+968]
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
