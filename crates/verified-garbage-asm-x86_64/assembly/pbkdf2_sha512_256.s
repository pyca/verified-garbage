// The functions of `src/pbkdf2_sha512_256.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512_256_shani:
	lea rsp, [rsp-1800]
	mov rax, QWORD PTR [rsp+1808]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+240], rbx
	mov QWORD PTR [r8+248], rbp
	mov QWORD PTR [r8+256], r12
	mov QWORD PTR [r8+264], r13
	mov QWORD PTR [r8+272], r14
	mov QWORD PTR [r8+280], r15
	mov r15, r8
	mov QWORD PTR [r15+288], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+296], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 880
	call {vg_sha512_256_init_core}
	mov rdi, r15
	add rdi, 880
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rdi, r15
	add rdi, 880
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1136
	mov rcx, r15
	call {vg_sha512_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 1136
	mov ecx, 32
21:
	mov rdi, r15
	add rdi, 304
	mov rsi, r15
	add rsi, 496
	mov r8, r15
	call {vg_hmac_sha512_256_init_scratch_shani}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+304]
	mov BYTE PTR [r15+r14*1+688], al
	add r14, 1
	cmp r14, 192
	jne 22b
	mov rdi, r15
	add rdi, 688
	mov esi, 128
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rbp, r13
	mov r13, QWORD PTR [r15+288]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+688]
	mov BYTE PTR [r15+r14*1+880], al
	add r14, 1
	cmp r14, 192
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+1200], eax
	mov rdi, r15
	add rdi, 880
	mov rsi, rbp
	add rsi, 128
	mov rdx, r15
	add rdx, 1200
	mov ecx, 4
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rdi, r15
	add rdi, 880
	mov rsi, r15
	add rsi, 496
	mov rdx, rbp
	add rdx, 132
	mov rcx, r15
	add rcx, 1072
	mov r8, r15
	call {vg_hmac_sha512_256_finalize_scratch_shani}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+1072]
	mov BYTE PTR [r15+r14*1+1104], al
	add r14, 1
	cmp r14, 32
	jne 27b
	mov rdi, r15
	add rdi, 304
	mov rsi, r15
	add rsi, 1072
	mov rdx, QWORD PTR [r15+296]
	mov rcx, r15
	add rcx, 1104
	mov r8, r15
	call {vg_pbkdf2_hmac_sha512_256_iterate_shani}
	mov ecx, 32
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+1104]
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
	mov rbx, QWORD PTR [r15+240]
	mov rbp, QWORD PTR [r15+248]
	mov r12, QWORD PTR [r15+256]
	mov r13, QWORD PTR [r15+264]
	mov r14, QWORD PTR [r15+272]
	mov r15, QWORD PTR [r15+280]
	lea rsp, [rsp+1800]
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
	lea rsp, [rsp-1824]
	mov QWORD PTR [rsp+1816], r11
	movdqu XMMWORD PTR [rsp+1800], xmm0
	vmovdqu YMMWORD PTR [rsp+1768], ymm0
	vmovdqu YMMWORD PTR [rsp+1736], ymm0
	vmovdqu YMMWORD PTR [rsp+1704], ymm0
	vmovdqu YMMWORD PTR [rsp+1672], ymm0
	vmovdqu YMMWORD PTR [rsp+1640], ymm0
	vmovdqu YMMWORD PTR [rsp+1608], ymm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1824]
	jmp 212f
211:
	xor r11d, r11d
	lea rsp, [rsp-1824]
	mov QWORD PTR [rsp+1816], r11
	vmovdqu YMMWORD PTR [rsp+1784], ymm0
	vmovdqu YMMWORD PTR [rsp+1752], ymm0
	vmovdqu YMMWORD PTR [rsp+1720], ymm0
	vmovdqu YMMWORD PTR [rsp+1688], ymm0
	vmovdqu YMMWORD PTR [rsp+1656], ymm0
	vmovdqu YMMWORD PTR [rsp+1624], ymm0
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1824]
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

vg_pbkdf2_hmac_sha512_256_avx2:
	lea rsp, [rsp-3128]
	mov rax, QWORD PTR [rsp+3136]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+1568], rbx
	mov QWORD PTR [r8+1576], rbp
	mov QWORD PTR [r8+1584], r12
	mov QWORD PTR [r8+1592], r13
	mov QWORD PTR [r8+1600], r14
	mov QWORD PTR [r8+1608], r15
	mov r15, r8
	mov QWORD PTR [r15+1616], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+1624], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 2208
	call {vg_sha512_256_init_core}
	mov rdi, r15
	add rdi, 2208
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rdi, r15
	add rdi, 2208
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2464
	mov rcx, r15
	call {vg_sha512_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 2464
	mov ecx, 32
21:
	mov rdi, r15
	add rdi, 1632
	mov rsi, r15
	add rsi, 1824
	mov r8, r15
	call {vg_hmac_sha512_256_init_scratch_avx2}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+1632]
	mov BYTE PTR [r15+r14*1+2016], al
	add r14, 1
	cmp r14, 192
	jne 22b
	mov rdi, r15
	add rdi, 2016
	mov esi, 128
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rbp, r13
	mov r13, QWORD PTR [r15+1616]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+2016]
	mov BYTE PTR [r15+r14*1+2208], al
	add r14, 1
	cmp r14, 192
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+2528], eax
	mov rdi, r15
	add rdi, 2208
	mov rsi, rbp
	add rsi, 128
	mov rdx, r15
	add rdx, 2528
	mov ecx, 4
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rdi, r15
	add rdi, 2208
	mov rsi, r15
	add rsi, 1824
	mov rdx, rbp
	add rdx, 132
	mov rcx, r15
	add rcx, 2400
	mov r8, r15
	call {vg_hmac_sha512_256_finalize_scratch_avx2}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+2400]
	mov BYTE PTR [r15+r14*1+2432], al
	add r14, 1
	cmp r14, 32
	jne 27b
	mov rdi, r15
	add rdi, 1632
	mov rsi, r15
	add rsi, 2400
	mov rdx, QWORD PTR [r15+1624]
	mov rcx, r15
	add rcx, 2432
	mov r8, r15
	call {vg_pbkdf2_hmac_sha512_256_iterate_avx2}
	mov ecx, 32
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+2432]
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
	mov rbx, QWORD PTR [r15+1568]
	mov rbp, QWORD PTR [r15+1576]
	mov r12, QWORD PTR [r15+1584]
	mov r13, QWORD PTR [r15+1592]
	mov r14, QWORD PTR [r15+1600]
	mov r15, QWORD PTR [r15+1608]
	lea rsp, [rsp+3128]
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
	lea rsp, [rsp-3152]
	mov QWORD PTR [rsp+3144], r11
	movdqu XMMWORD PTR [rsp+3128], xmm0
	vmovdqu YMMWORD PTR [rsp+3096], ymm0
	vmovdqu YMMWORD PTR [rsp+3064], ymm0
	vmovdqu YMMWORD PTR [rsp+3032], ymm0
	vmovdqu YMMWORD PTR [rsp+3000], ymm0
	vmovdqu YMMWORD PTR [rsp+2968], ymm0
	vmovdqu YMMWORD PTR [rsp+2936], ymm0
	vmovdqu YMMWORD PTR [rsp+2904], ymm0
	vmovdqu YMMWORD PTR [rsp+2872], ymm0
	vmovdqu YMMWORD PTR [rsp+2840], ymm0
	vmovdqu YMMWORD PTR [rsp+2808], ymm0
	vmovdqu YMMWORD PTR [rsp+2776], ymm0
	vmovdqu YMMWORD PTR [rsp+2744], ymm0
	vmovdqu YMMWORD PTR [rsp+2712], ymm0
	vmovdqu YMMWORD PTR [rsp+2680], ymm0
	vmovdqu YMMWORD PTR [rsp+2648], ymm0
	vmovdqu YMMWORD PTR [rsp+2616], ymm0
	vmovdqu YMMWORD PTR [rsp+2584], ymm0
	vmovdqu YMMWORD PTR [rsp+2552], ymm0
	vmovdqu YMMWORD PTR [rsp+2520], ymm0
	vmovdqu YMMWORD PTR [rsp+2488], ymm0
	vmovdqu YMMWORD PTR [rsp+2456], ymm0
	vmovdqu YMMWORD PTR [rsp+2424], ymm0
	vmovdqu YMMWORD PTR [rsp+2392], ymm0
	vmovdqu YMMWORD PTR [rsp+2360], ymm0
	vmovdqu YMMWORD PTR [rsp+2328], ymm0
	vmovdqu YMMWORD PTR [rsp+2296], ymm0
	vmovdqu YMMWORD PTR [rsp+2264], ymm0
	vmovdqu YMMWORD PTR [rsp+2232], ymm0
	vmovdqu YMMWORD PTR [rsp+2200], ymm0
	vmovdqu YMMWORD PTR [rsp+2168], ymm0
	vmovdqu YMMWORD PTR [rsp+2136], ymm0
	vmovdqu YMMWORD PTR [rsp+2104], ymm0
	vmovdqu YMMWORD PTR [rsp+2072], ymm0
	vmovdqu YMMWORD PTR [rsp+2040], ymm0
	vmovdqu YMMWORD PTR [rsp+2008], ymm0
	vmovdqu YMMWORD PTR [rsp+1976], ymm0
	vmovdqu YMMWORD PTR [rsp+1944], ymm0
	vmovdqu YMMWORD PTR [rsp+1912], ymm0
	vmovdqu YMMWORD PTR [rsp+1880], ymm0
	vmovdqu YMMWORD PTR [rsp+1848], ymm0
	vmovdqu YMMWORD PTR [rsp+1816], ymm0
	vmovdqu YMMWORD PTR [rsp+1784], ymm0
	vmovdqu YMMWORD PTR [rsp+1752], ymm0
	vmovdqu YMMWORD PTR [rsp+1720], ymm0
	vmovdqu YMMWORD PTR [rsp+1688], ymm0
	vmovdqu YMMWORD PTR [rsp+1656], ymm0
	vmovdqu YMMWORD PTR [rsp+1624], ymm0
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3152]
	jmp 212f
211:
	xor r11d, r11d
	lea rsp, [rsp-3152]
	mov QWORD PTR [rsp+3144], r11
	vmovdqu YMMWORD PTR [rsp+3112], ymm0
	vmovdqu YMMWORD PTR [rsp+3080], ymm0
	vmovdqu YMMWORD PTR [rsp+3048], ymm0
	vmovdqu YMMWORD PTR [rsp+3016], ymm0
	vmovdqu YMMWORD PTR [rsp+2984], ymm0
	vmovdqu YMMWORD PTR [rsp+2952], ymm0
	vmovdqu YMMWORD PTR [rsp+2920], ymm0
	vmovdqu YMMWORD PTR [rsp+2888], ymm0
	vmovdqu YMMWORD PTR [rsp+2856], ymm0
	vmovdqu YMMWORD PTR [rsp+2824], ymm0
	vmovdqu YMMWORD PTR [rsp+2792], ymm0
	vmovdqu YMMWORD PTR [rsp+2760], ymm0
	vmovdqu YMMWORD PTR [rsp+2728], ymm0
	vmovdqu YMMWORD PTR [rsp+2696], ymm0
	vmovdqu YMMWORD PTR [rsp+2664], ymm0
	vmovdqu YMMWORD PTR [rsp+2632], ymm0
	vmovdqu YMMWORD PTR [rsp+2600], ymm0
	vmovdqu YMMWORD PTR [rsp+2568], ymm0
	vmovdqu YMMWORD PTR [rsp+2536], ymm0
	vmovdqu YMMWORD PTR [rsp+2504], ymm0
	vmovdqu YMMWORD PTR [rsp+2472], ymm0
	vmovdqu YMMWORD PTR [rsp+2440], ymm0
	vmovdqu YMMWORD PTR [rsp+2408], ymm0
	vmovdqu YMMWORD PTR [rsp+2376], ymm0
	vmovdqu YMMWORD PTR [rsp+2344], ymm0
	vmovdqu YMMWORD PTR [rsp+2312], ymm0
	vmovdqu YMMWORD PTR [rsp+2280], ymm0
	vmovdqu YMMWORD PTR [rsp+2248], ymm0
	vmovdqu YMMWORD PTR [rsp+2216], ymm0
	vmovdqu YMMWORD PTR [rsp+2184], ymm0
	vmovdqu YMMWORD PTR [rsp+2152], ymm0
	vmovdqu YMMWORD PTR [rsp+2120], ymm0
	vmovdqu YMMWORD PTR [rsp+2088], ymm0
	vmovdqu YMMWORD PTR [rsp+2056], ymm0
	vmovdqu YMMWORD PTR [rsp+2024], ymm0
	vmovdqu YMMWORD PTR [rsp+1992], ymm0
	vmovdqu YMMWORD PTR [rsp+1960], ymm0
	vmovdqu YMMWORD PTR [rsp+1928], ymm0
	vmovdqu YMMWORD PTR [rsp+1896], ymm0
	vmovdqu YMMWORD PTR [rsp+1864], ymm0
	vmovdqu YMMWORD PTR [rsp+1832], ymm0
	vmovdqu YMMWORD PTR [rsp+1800], ymm0
	vmovdqu YMMWORD PTR [rsp+1768], ymm0
	vmovdqu YMMWORD PTR [rsp+1736], ymm0
	vmovdqu YMMWORD PTR [rsp+1704], ymm0
	vmovdqu YMMWORD PTR [rsp+1672], ymm0
	vmovdqu YMMWORD PTR [rsp+1640], ymm0
	vmovdqu YMMWORD PTR [rsp+1608], ymm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3152]
212:
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

vg_pbkdf2_hmac_sha512_256:
	lea rsp, [rsp-1992]
	mov rax, QWORD PTR [rsp+2000]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+432], rbx
	mov QWORD PTR [r8+440], rbp
	mov QWORD PTR [r8+448], r12
	mov QWORD PTR [r8+456], r13
	mov QWORD PTR [r8+464], r14
	mov QWORD PTR [r8+472], r15
	mov r15, r8
	mov QWORD PTR [r15+480], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+488], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 1072
	call {vg_sha512_256_init_core}
	mov rdi, r15
	add rdi, 1072
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rdi, r15
	add rdi, 1072
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1328
	mov rcx, r15
	call {vg_sha512_finalize_scratch}
	mov rdx, r15
	add rdx, 1328
	mov ecx, 32
21:
	mov rdi, r15
	add rdi, 496
	mov rsi, r15
	add rsi, 688
	mov r8, r15
	call {vg_hmac_sha512_256_init_scratch}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+496]
	mov BYTE PTR [r15+r14*1+880], al
	add r14, 1
	cmp r14, 192
	jne 22b
	mov rdi, r15
	add rdi, 880
	mov esi, 128
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rbp, r13
	mov r13, QWORD PTR [r15+480]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+880]
	mov BYTE PTR [r15+r14*1+1072], al
	add r14, 1
	cmp r14, 192
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+1392], eax
	mov rdi, r15
	add rdi, 1072
	mov rsi, rbp
	add rsi, 128
	mov rdx, r15
	add rdx, 1392
	mov ecx, 4
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rdi, r15
	add rdi, 1072
	mov rsi, r15
	add rsi, 688
	mov rdx, rbp
	add rdx, 132
	mov rcx, r15
	add rcx, 1264
	mov r8, r15
	call {vg_hmac_sha512_256_finalize_scratch}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+1264]
	mov BYTE PTR [r15+r14*1+1296], al
	add r14, 1
	cmp r14, 32
	jne 27b
	mov rdi, r15
	add rdi, 496
	mov rsi, r15
	add rsi, 1264
	mov rdx, QWORD PTR [r15+488]
	mov rcx, r15
	add rcx, 1296
	mov r8, r15
	call {vg_pbkdf2_hmac_sha512_256_iterate}
	mov ecx, 32
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+1296]
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
	mov rbx, QWORD PTR [r15+432]
	mov rbp, QWORD PTR [r15+440]
	mov r12, QWORD PTR [r15+448]
	mov r13, QWORD PTR [r15+456]
	mov r14, QWORD PTR [r15+464]
	mov r15, QWORD PTR [r15+472]
	lea rsp, [rsp+1992]
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
	lea rsp, [rsp-2016]
	mov QWORD PTR [rsp+2008], r11
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+2016]
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
