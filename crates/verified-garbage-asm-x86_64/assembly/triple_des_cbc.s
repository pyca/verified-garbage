// The functions of `src/triple_des_cbc.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_cbc_encrypt_chained:
	lea rsp, [rsp-976]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+904], rbx
	mov QWORD PTR [r9+912], rbp
	mov QWORD PTR [r9+920], r12
	mov QWORD PTR [r9+928], r13
	mov QWORD PTR [r9+936], r14
	mov QWORD PTR [r9+944], r15
	movq xmm15, rsi
	test rcx, rcx
	je 20f
	mov rax, QWORD PTR [rdx]
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rdx], rax
	jmp 21f
20:
21:
	mov r12, rdx
	mov r13, rcx
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+520], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+528], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+536], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+544], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [r9+552], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [r9+560], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [r9+568], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [r9+576], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r9+584], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [r9+592], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [r9+600], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [r9+608], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [r9+616], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [r9+624], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [r9+632], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [r9+640], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [r9+648], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [r9+656], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [r9+664], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [r9+672], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [r9+680], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [r9+688], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [r9+696], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [r9+704], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [r9+712], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [r9+720], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [r9+728], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [r9+736], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [r9+744], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [r9+752], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9+760], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+768], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [r9+776], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [r9+784], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [r9+792], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [r9+800], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [r9+808], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [r9+816], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [r9+824], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [r9+832], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [r9+840], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [r9+848], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [r9+856], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [r9+864], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [r9+872], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [r9+880], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [r9+888], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [r9+896], rax
	test r13, r13
	je 22f
24:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r9+512], rax
	mov rdi, r9
	add rdi, 520
	mov rsi, r9
	add rsi, 512
	mov rdx, r9
	call {vg_triple_des_encrypt_block}
	mov r9, rdx
	mov rax, QWORD PTR [r9+512]
	mov QWORD PTR [r12], rax
	sub r13, 1
	je 25f
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r9+512]
	mov QWORD PTR [r12+8], rax
	jmp 26f
25:
26:
	add r12, 8
	test r13, r13
	jne 24b
	movq rax, xmm15
	mov rbp, QWORD PTR [r9+512]
	mov QWORD PTR [rax], rbp
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+904]
	mov rbp, QWORD PTR [r9+912]
	mov r12, QWORD PTR [r9+920]
	mov r13, QWORD PTR [r9+928]
	mov r14, QWORD PTR [r9+936]
	mov r15, QWORD PTR [r9+944]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	lea rsp, [rsp+976]
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
	lea rsp, [rsp-984]
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+984]
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

vg_triple_des_cbc_decrypt_chained_avx512:
	lea rsp, [rsp-2128]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+2056], rbx
	mov QWORD PTR [r9+2064], rbp
	mov QWORD PTR [r9+2072], r12
	mov QWORD PTR [r9+2080], r13
	mov QWORD PTR [r9+2088], r14
	mov QWORD PTR [r9+2096], r15
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [r9], rax
	test rcx, rcx
	je 20f
	mov rax, rcx
	sub rax, 1
	shl rax, 3
	add rax, rdx
	mov rbx, QWORD PTR [rax]
	mov QWORD PTR [rsi], rbx
	jmp 21f
20:
21:
	mov r15, rdi
	mov r13, r9
	mov r12, rdx
	mov r14, rcx
	test r14, r14
	je 22f
24:
	movabs rcx, 256
	cmp r14, 256
	jb 25f
	jmp 26f
25:
	mov rcx, r14
26:
	mov rax, r9
	add rax, 8
	mov rbx, r12
	mov r10, rcx
27:
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [rax], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 27b
	mov rdi, r15
	mov rsi, r12
	mov rdx, r10
	call {vg_triple_des_ecb_decrypt_avx512_core}
	mov r9, r13
	movabs rcx, 256
	cmp r14, 256
	jb 28f
	jmp 29f
28:
	mov rcx, r14
29:
	mov rbx, r12
	mov r10, rcx
	mov rax, r9
210:
	mov rbp, QWORD PTR [rbx]
	xor rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 210b
	mov rax, r10
	shl rax, 3
	add rax, r9
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9], rbp
	mov r12, rbx
	sub r14, r10
	jne 24b
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+2056]
	mov rbp, QWORD PTR [r9+2064]
	mov r12, QWORD PTR [r9+2072]
	mov r13, QWORD PTR [r9+2080]
	mov r14, QWORD PTR [r9+2088]
	mov r15, QWORD PTR [r9+2096]
	lea rsp, [rsp+2128]
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
	lea rsp, [rsp-3176]
	mov QWORD PTR [rsp+3168], r11
	movdqu XMMWORD PTR [rsp+3152], xmm0
	vmovdqu YMMWORD PTR [rsp+3120], ymm0
	vmovdqu YMMWORD PTR [rsp+3088], ymm0
	vmovdqu YMMWORD PTR [rsp+3056], ymm0
	vmovdqu YMMWORD PTR [rsp+3024], ymm0
	vmovdqu YMMWORD PTR [rsp+2992], ymm0
	vmovdqu YMMWORD PTR [rsp+2960], ymm0
	vmovdqu YMMWORD PTR [rsp+2928], ymm0
	vmovdqu YMMWORD PTR [rsp+2896], ymm0
	vmovdqu YMMWORD PTR [rsp+2864], ymm0
	vmovdqu YMMWORD PTR [rsp+2832], ymm0
	vmovdqu YMMWORD PTR [rsp+2800], ymm0
	vmovdqu YMMWORD PTR [rsp+2768], ymm0
	vmovdqu YMMWORD PTR [rsp+2736], ymm0
	vmovdqu YMMWORD PTR [rsp+2704], ymm0
	vmovdqu YMMWORD PTR [rsp+2672], ymm0
	vmovdqu YMMWORD PTR [rsp+2640], ymm0
	vmovdqu YMMWORD PTR [rsp+2608], ymm0
	vmovdqu YMMWORD PTR [rsp+2576], ymm0
	vmovdqu YMMWORD PTR [rsp+2544], ymm0
	vmovdqu YMMWORD PTR [rsp+2512], ymm0
	vmovdqu YMMWORD PTR [rsp+2480], ymm0
	vmovdqu YMMWORD PTR [rsp+2448], ymm0
	vmovdqu YMMWORD PTR [rsp+2416], ymm0
	vmovdqu YMMWORD PTR [rsp+2384], ymm0
	vmovdqu YMMWORD PTR [rsp+2352], ymm0
	vmovdqu YMMWORD PTR [rsp+2320], ymm0
	vmovdqu YMMWORD PTR [rsp+2288], ymm0
	vmovdqu YMMWORD PTR [rsp+2256], ymm0
	vmovdqu YMMWORD PTR [rsp+2224], ymm0
	vmovdqu YMMWORD PTR [rsp+2192], ymm0
	vmovdqu YMMWORD PTR [rsp+2160], ymm0
	vmovdqu YMMWORD PTR [rsp+2128], ymm0
	vmovdqu YMMWORD PTR [rsp+2096], ymm0
	vmovdqu YMMWORD PTR [rsp+2064], ymm0
	vmovdqu YMMWORD PTR [rsp+2032], ymm0
	vmovdqu YMMWORD PTR [rsp+2000], ymm0
	vmovdqu YMMWORD PTR [rsp+1968], ymm0
	vmovdqu YMMWORD PTR [rsp+1936], ymm0
	vmovdqu YMMWORD PTR [rsp+1904], ymm0
	vmovdqu YMMWORD PTR [rsp+1872], ymm0
	vmovdqu YMMWORD PTR [rsp+1840], ymm0
	vmovdqu YMMWORD PTR [rsp+1808], ymm0
	vmovdqu YMMWORD PTR [rsp+1776], ymm0
	vmovdqu YMMWORD PTR [rsp+1744], ymm0
	vmovdqu YMMWORD PTR [rsp+1712], ymm0
	vmovdqu YMMWORD PTR [rsp+1680], ymm0
	vmovdqu YMMWORD PTR [rsp+1648], ymm0
	vmovdqu YMMWORD PTR [rsp+1616], ymm0
	vmovdqu YMMWORD PTR [rsp+1584], ymm0
	vmovdqu YMMWORD PTR [rsp+1552], ymm0
	vmovdqu YMMWORD PTR [rsp+1520], ymm0
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
	lea rsp, [rsp+3176]
	jmp 212f
211:
	xor r11d, r11d
	lea rsp, [rsp-3176]
	mov QWORD PTR [rsp+3168], r11
	vmovdqu YMMWORD PTR [rsp+3136], ymm0
	vmovdqu YMMWORD PTR [rsp+3104], ymm0
	vmovdqu YMMWORD PTR [rsp+3072], ymm0
	vmovdqu YMMWORD PTR [rsp+3040], ymm0
	vmovdqu YMMWORD PTR [rsp+3008], ymm0
	vmovdqu YMMWORD PTR [rsp+2976], ymm0
	vmovdqu YMMWORD PTR [rsp+2944], ymm0
	vmovdqu YMMWORD PTR [rsp+2912], ymm0
	vmovdqu YMMWORD PTR [rsp+2880], ymm0
	vmovdqu YMMWORD PTR [rsp+2848], ymm0
	vmovdqu YMMWORD PTR [rsp+2816], ymm0
	vmovdqu YMMWORD PTR [rsp+2784], ymm0
	vmovdqu YMMWORD PTR [rsp+2752], ymm0
	vmovdqu YMMWORD PTR [rsp+2720], ymm0
	vmovdqu YMMWORD PTR [rsp+2688], ymm0
	vmovdqu YMMWORD PTR [rsp+2656], ymm0
	vmovdqu YMMWORD PTR [rsp+2624], ymm0
	vmovdqu YMMWORD PTR [rsp+2592], ymm0
	vmovdqu YMMWORD PTR [rsp+2560], ymm0
	vmovdqu YMMWORD PTR [rsp+2528], ymm0
	vmovdqu YMMWORD PTR [rsp+2496], ymm0
	vmovdqu YMMWORD PTR [rsp+2464], ymm0
	vmovdqu YMMWORD PTR [rsp+2432], ymm0
	vmovdqu YMMWORD PTR [rsp+2400], ymm0
	vmovdqu YMMWORD PTR [rsp+2368], ymm0
	vmovdqu YMMWORD PTR [rsp+2336], ymm0
	vmovdqu YMMWORD PTR [rsp+2304], ymm0
	vmovdqu YMMWORD PTR [rsp+2272], ymm0
	vmovdqu YMMWORD PTR [rsp+2240], ymm0
	vmovdqu YMMWORD PTR [rsp+2208], ymm0
	vmovdqu YMMWORD PTR [rsp+2176], ymm0
	vmovdqu YMMWORD PTR [rsp+2144], ymm0
	vmovdqu YMMWORD PTR [rsp+2112], ymm0
	vmovdqu YMMWORD PTR [rsp+2080], ymm0
	vmovdqu YMMWORD PTR [rsp+2048], ymm0
	vmovdqu YMMWORD PTR [rsp+2016], ymm0
	vmovdqu YMMWORD PTR [rsp+1984], ymm0
	vmovdqu YMMWORD PTR [rsp+1952], ymm0
	vmovdqu YMMWORD PTR [rsp+1920], ymm0
	vmovdqu YMMWORD PTR [rsp+1888], ymm0
	vmovdqu YMMWORD PTR [rsp+1856], ymm0
	vmovdqu YMMWORD PTR [rsp+1824], ymm0
	vmovdqu YMMWORD PTR [rsp+1792], ymm0
	vmovdqu YMMWORD PTR [rsp+1760], ymm0
	vmovdqu YMMWORD PTR [rsp+1728], ymm0
	vmovdqu YMMWORD PTR [rsp+1696], ymm0
	vmovdqu YMMWORD PTR [rsp+1664], ymm0
	vmovdqu YMMWORD PTR [rsp+1632], ymm0
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
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
	lea rsp, [rsp+3176]
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

vg_triple_des_cbc_decrypt_chained_avx2:
	lea rsp, [rsp-2128]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+2056], rbx
	mov QWORD PTR [r9+2064], rbp
	mov QWORD PTR [r9+2072], r12
	mov QWORD PTR [r9+2080], r13
	mov QWORD PTR [r9+2088], r14
	mov QWORD PTR [r9+2096], r15
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [r9], rax
	test rcx, rcx
	je 20f
	mov rax, rcx
	sub rax, 1
	shl rax, 3
	add rax, rdx
	mov rbx, QWORD PTR [rax]
	mov QWORD PTR [rsi], rbx
	jmp 21f
20:
21:
	mov r15, rdi
	mov r13, r9
	mov r12, rdx
	mov r14, rcx
	test r14, r14
	je 22f
24:
	movabs rcx, 256
	cmp r14, 256
	jb 25f
	jmp 26f
25:
	mov rcx, r14
26:
	mov rax, r9
	add rax, 8
	mov rbx, r12
	mov r10, rcx
27:
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [rax], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 27b
	mov rdi, r15
	mov rsi, r12
	mov rdx, r10
	call {vg_triple_des_ecb_decrypt_avx2_core}
	mov r9, r13
	movabs rcx, 256
	cmp r14, 256
	jb 28f
	jmp 29f
28:
	mov rcx, r14
29:
	mov rbx, r12
	mov r10, rcx
	mov rax, r9
210:
	mov rbp, QWORD PTR [rbx]
	xor rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 210b
	mov rax, r10
	shl rax, 3
	add rax, r9
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9], rbp
	mov r12, rbx
	sub r14, r10
	jne 24b
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+2056]
	mov rbp, QWORD PTR [r9+2064]
	mov r12, QWORD PTR [r9+2072]
	mov r13, QWORD PTR [r9+2080]
	mov r14, QWORD PTR [r9+2088]
	mov r15, QWORD PTR [r9+2096]
	lea rsp, [rsp+2128]
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
	lea rsp, [rsp-3176]
	mov QWORD PTR [rsp+3168], r11
	movdqu XMMWORD PTR [rsp+3152], xmm0
	vmovdqu YMMWORD PTR [rsp+3120], ymm0
	vmovdqu YMMWORD PTR [rsp+3088], ymm0
	vmovdqu YMMWORD PTR [rsp+3056], ymm0
	vmovdqu YMMWORD PTR [rsp+3024], ymm0
	vmovdqu YMMWORD PTR [rsp+2992], ymm0
	vmovdqu YMMWORD PTR [rsp+2960], ymm0
	vmovdqu YMMWORD PTR [rsp+2928], ymm0
	vmovdqu YMMWORD PTR [rsp+2896], ymm0
	vmovdqu YMMWORD PTR [rsp+2864], ymm0
	vmovdqu YMMWORD PTR [rsp+2832], ymm0
	vmovdqu YMMWORD PTR [rsp+2800], ymm0
	vmovdqu YMMWORD PTR [rsp+2768], ymm0
	vmovdqu YMMWORD PTR [rsp+2736], ymm0
	vmovdqu YMMWORD PTR [rsp+2704], ymm0
	vmovdqu YMMWORD PTR [rsp+2672], ymm0
	vmovdqu YMMWORD PTR [rsp+2640], ymm0
	vmovdqu YMMWORD PTR [rsp+2608], ymm0
	vmovdqu YMMWORD PTR [rsp+2576], ymm0
	vmovdqu YMMWORD PTR [rsp+2544], ymm0
	vmovdqu YMMWORD PTR [rsp+2512], ymm0
	vmovdqu YMMWORD PTR [rsp+2480], ymm0
	vmovdqu YMMWORD PTR [rsp+2448], ymm0
	vmovdqu YMMWORD PTR [rsp+2416], ymm0
	vmovdqu YMMWORD PTR [rsp+2384], ymm0
	vmovdqu YMMWORD PTR [rsp+2352], ymm0
	vmovdqu YMMWORD PTR [rsp+2320], ymm0
	vmovdqu YMMWORD PTR [rsp+2288], ymm0
	vmovdqu YMMWORD PTR [rsp+2256], ymm0
	vmovdqu YMMWORD PTR [rsp+2224], ymm0
	vmovdqu YMMWORD PTR [rsp+2192], ymm0
	vmovdqu YMMWORD PTR [rsp+2160], ymm0
	vmovdqu YMMWORD PTR [rsp+2128], ymm0
	vmovdqu YMMWORD PTR [rsp+2096], ymm0
	vmovdqu YMMWORD PTR [rsp+2064], ymm0
	vmovdqu YMMWORD PTR [rsp+2032], ymm0
	vmovdqu YMMWORD PTR [rsp+2000], ymm0
	vmovdqu YMMWORD PTR [rsp+1968], ymm0
	vmovdqu YMMWORD PTR [rsp+1936], ymm0
	vmovdqu YMMWORD PTR [rsp+1904], ymm0
	vmovdqu YMMWORD PTR [rsp+1872], ymm0
	vmovdqu YMMWORD PTR [rsp+1840], ymm0
	vmovdqu YMMWORD PTR [rsp+1808], ymm0
	vmovdqu YMMWORD PTR [rsp+1776], ymm0
	vmovdqu YMMWORD PTR [rsp+1744], ymm0
	vmovdqu YMMWORD PTR [rsp+1712], ymm0
	vmovdqu YMMWORD PTR [rsp+1680], ymm0
	vmovdqu YMMWORD PTR [rsp+1648], ymm0
	vmovdqu YMMWORD PTR [rsp+1616], ymm0
	vmovdqu YMMWORD PTR [rsp+1584], ymm0
	vmovdqu YMMWORD PTR [rsp+1552], ymm0
	vmovdqu YMMWORD PTR [rsp+1520], ymm0
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
	lea rsp, [rsp+3176]
	jmp 212f
211:
	xor r11d, r11d
	lea rsp, [rsp-3176]
	mov QWORD PTR [rsp+3168], r11
	vmovdqu YMMWORD PTR [rsp+3136], ymm0
	vmovdqu YMMWORD PTR [rsp+3104], ymm0
	vmovdqu YMMWORD PTR [rsp+3072], ymm0
	vmovdqu YMMWORD PTR [rsp+3040], ymm0
	vmovdqu YMMWORD PTR [rsp+3008], ymm0
	vmovdqu YMMWORD PTR [rsp+2976], ymm0
	vmovdqu YMMWORD PTR [rsp+2944], ymm0
	vmovdqu YMMWORD PTR [rsp+2912], ymm0
	vmovdqu YMMWORD PTR [rsp+2880], ymm0
	vmovdqu YMMWORD PTR [rsp+2848], ymm0
	vmovdqu YMMWORD PTR [rsp+2816], ymm0
	vmovdqu YMMWORD PTR [rsp+2784], ymm0
	vmovdqu YMMWORD PTR [rsp+2752], ymm0
	vmovdqu YMMWORD PTR [rsp+2720], ymm0
	vmovdqu YMMWORD PTR [rsp+2688], ymm0
	vmovdqu YMMWORD PTR [rsp+2656], ymm0
	vmovdqu YMMWORD PTR [rsp+2624], ymm0
	vmovdqu YMMWORD PTR [rsp+2592], ymm0
	vmovdqu YMMWORD PTR [rsp+2560], ymm0
	vmovdqu YMMWORD PTR [rsp+2528], ymm0
	vmovdqu YMMWORD PTR [rsp+2496], ymm0
	vmovdqu YMMWORD PTR [rsp+2464], ymm0
	vmovdqu YMMWORD PTR [rsp+2432], ymm0
	vmovdqu YMMWORD PTR [rsp+2400], ymm0
	vmovdqu YMMWORD PTR [rsp+2368], ymm0
	vmovdqu YMMWORD PTR [rsp+2336], ymm0
	vmovdqu YMMWORD PTR [rsp+2304], ymm0
	vmovdqu YMMWORD PTR [rsp+2272], ymm0
	vmovdqu YMMWORD PTR [rsp+2240], ymm0
	vmovdqu YMMWORD PTR [rsp+2208], ymm0
	vmovdqu YMMWORD PTR [rsp+2176], ymm0
	vmovdqu YMMWORD PTR [rsp+2144], ymm0
	vmovdqu YMMWORD PTR [rsp+2112], ymm0
	vmovdqu YMMWORD PTR [rsp+2080], ymm0
	vmovdqu YMMWORD PTR [rsp+2048], ymm0
	vmovdqu YMMWORD PTR [rsp+2016], ymm0
	vmovdqu YMMWORD PTR [rsp+1984], ymm0
	vmovdqu YMMWORD PTR [rsp+1952], ymm0
	vmovdqu YMMWORD PTR [rsp+1920], ymm0
	vmovdqu YMMWORD PTR [rsp+1888], ymm0
	vmovdqu YMMWORD PTR [rsp+1856], ymm0
	vmovdqu YMMWORD PTR [rsp+1824], ymm0
	vmovdqu YMMWORD PTR [rsp+1792], ymm0
	vmovdqu YMMWORD PTR [rsp+1760], ymm0
	vmovdqu YMMWORD PTR [rsp+1728], ymm0
	vmovdqu YMMWORD PTR [rsp+1696], ymm0
	vmovdqu YMMWORD PTR [rsp+1664], ymm0
	vmovdqu YMMWORD PTR [rsp+1632], ymm0
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
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
	lea rsp, [rsp+3176]
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

vg_triple_des_cbc_decrypt_chained:
	lea rsp, [rsp-2128]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+2056], rbx
	mov QWORD PTR [r9+2064], rbp
	mov QWORD PTR [r9+2072], r12
	mov QWORD PTR [r9+2080], r13
	mov QWORD PTR [r9+2088], r14
	mov QWORD PTR [r9+2096], r15
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [r9], rax
	test rcx, rcx
	je 20f
	mov rax, rcx
	sub rax, 1
	shl rax, 3
	add rax, rdx
	mov rbx, QWORD PTR [rax]
	mov QWORD PTR [rsi], rbx
	jmp 21f
20:
21:
	mov r15, rdi
	mov r13, r9
	mov r12, rdx
	mov r14, rcx
	test r14, r14
	je 22f
24:
	movabs rcx, 256
	cmp r14, 256
	jb 25f
	jmp 26f
25:
	mov rcx, r14
26:
	mov rax, r9
	add rax, 8
	mov rbx, r12
	mov r10, rcx
27:
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [rax], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 27b
	mov rdi, r15
	mov rsi, r12
	mov rdx, r10
	call {vg_triple_des_ecb_decrypt_core}
	mov r9, r13
	movabs rcx, 256
	cmp r14, 256
	jb 28f
	jmp 29f
28:
	mov rcx, r14
29:
	mov rbx, r12
	mov r10, rcx
	mov rax, r9
210:
	mov rbp, QWORD PTR [rbx]
	xor rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 210b
	mov rax, r10
	shl rax, 3
	add rax, r9
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9], rbp
	mov r12, rbx
	sub r14, r10
	jne 24b
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+2056]
	mov rbp, QWORD PTR [r9+2064]
	mov r12, QWORD PTR [r9+2072]
	mov r13, QWORD PTR [r9+2080]
	mov r14, QWORD PTR [r9+2088]
	mov r15, QWORD PTR [r9+2096]
	lea rsp, [rsp+2128]
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
	lea rsp, [rsp-3176]
	mov QWORD PTR [rsp+3168], r11
	movdqu XMMWORD PTR [rsp+3152], xmm0
	movdqu XMMWORD PTR [rsp+3136], xmm0
	movdqu XMMWORD PTR [rsp+3120], xmm0
	movdqu XMMWORD PTR [rsp+3104], xmm0
	movdqu XMMWORD PTR [rsp+3088], xmm0
	movdqu XMMWORD PTR [rsp+3072], xmm0
	movdqu XMMWORD PTR [rsp+3056], xmm0
	movdqu XMMWORD PTR [rsp+3040], xmm0
	movdqu XMMWORD PTR [rsp+3024], xmm0
	movdqu XMMWORD PTR [rsp+3008], xmm0
	movdqu XMMWORD PTR [rsp+2992], xmm0
	movdqu XMMWORD PTR [rsp+2976], xmm0
	movdqu XMMWORD PTR [rsp+2960], xmm0
	movdqu XMMWORD PTR [rsp+2944], xmm0
	movdqu XMMWORD PTR [rsp+2928], xmm0
	movdqu XMMWORD PTR [rsp+2912], xmm0
	movdqu XMMWORD PTR [rsp+2896], xmm0
	movdqu XMMWORD PTR [rsp+2880], xmm0
	movdqu XMMWORD PTR [rsp+2864], xmm0
	movdqu XMMWORD PTR [rsp+2848], xmm0
	movdqu XMMWORD PTR [rsp+2832], xmm0
	movdqu XMMWORD PTR [rsp+2816], xmm0
	movdqu XMMWORD PTR [rsp+2800], xmm0
	movdqu XMMWORD PTR [rsp+2784], xmm0
	movdqu XMMWORD PTR [rsp+2768], xmm0
	movdqu XMMWORD PTR [rsp+2752], xmm0
	movdqu XMMWORD PTR [rsp+2736], xmm0
	movdqu XMMWORD PTR [rsp+2720], xmm0
	movdqu XMMWORD PTR [rsp+2704], xmm0
	movdqu XMMWORD PTR [rsp+2688], xmm0
	movdqu XMMWORD PTR [rsp+2672], xmm0
	movdqu XMMWORD PTR [rsp+2656], xmm0
	movdqu XMMWORD PTR [rsp+2640], xmm0
	movdqu XMMWORD PTR [rsp+2624], xmm0
	movdqu XMMWORD PTR [rsp+2608], xmm0
	movdqu XMMWORD PTR [rsp+2592], xmm0
	movdqu XMMWORD PTR [rsp+2576], xmm0
	movdqu XMMWORD PTR [rsp+2560], xmm0
	movdqu XMMWORD PTR [rsp+2544], xmm0
	movdqu XMMWORD PTR [rsp+2528], xmm0
	movdqu XMMWORD PTR [rsp+2512], xmm0
	movdqu XMMWORD PTR [rsp+2496], xmm0
	movdqu XMMWORD PTR [rsp+2480], xmm0
	movdqu XMMWORD PTR [rsp+2464], xmm0
	movdqu XMMWORD PTR [rsp+2448], xmm0
	movdqu XMMWORD PTR [rsp+2432], xmm0
	movdqu XMMWORD PTR [rsp+2416], xmm0
	movdqu XMMWORD PTR [rsp+2400], xmm0
	movdqu XMMWORD PTR [rsp+2384], xmm0
	movdqu XMMWORD PTR [rsp+2368], xmm0
	movdqu XMMWORD PTR [rsp+2352], xmm0
	movdqu XMMWORD PTR [rsp+2336], xmm0
	movdqu XMMWORD PTR [rsp+2320], xmm0
	movdqu XMMWORD PTR [rsp+2304], xmm0
	movdqu XMMWORD PTR [rsp+2288], xmm0
	movdqu XMMWORD PTR [rsp+2272], xmm0
	movdqu XMMWORD PTR [rsp+2256], xmm0
	movdqu XMMWORD PTR [rsp+2240], xmm0
	movdqu XMMWORD PTR [rsp+2224], xmm0
	movdqu XMMWORD PTR [rsp+2208], xmm0
	movdqu XMMWORD PTR [rsp+2192], xmm0
	movdqu XMMWORD PTR [rsp+2176], xmm0
	movdqu XMMWORD PTR [rsp+2160], xmm0
	movdqu XMMWORD PTR [rsp+2144], xmm0
	movdqu XMMWORD PTR [rsp+2128], xmm0
	movdqu XMMWORD PTR [rsp+2112], xmm0
	movdqu XMMWORD PTR [rsp+2096], xmm0
	movdqu XMMWORD PTR [rsp+2080], xmm0
	movdqu XMMWORD PTR [rsp+2064], xmm0
	movdqu XMMWORD PTR [rsp+2048], xmm0
	movdqu XMMWORD PTR [rsp+2032], xmm0
	movdqu XMMWORD PTR [rsp+2016], xmm0
	movdqu XMMWORD PTR [rsp+2000], xmm0
	movdqu XMMWORD PTR [rsp+1984], xmm0
	movdqu XMMWORD PTR [rsp+1968], xmm0
	movdqu XMMWORD PTR [rsp+1952], xmm0
	movdqu XMMWORD PTR [rsp+1936], xmm0
	movdqu XMMWORD PTR [rsp+1920], xmm0
	movdqu XMMWORD PTR [rsp+1904], xmm0
	movdqu XMMWORD PTR [rsp+1888], xmm0
	movdqu XMMWORD PTR [rsp+1872], xmm0
	movdqu XMMWORD PTR [rsp+1856], xmm0
	movdqu XMMWORD PTR [rsp+1840], xmm0
	movdqu XMMWORD PTR [rsp+1824], xmm0
	movdqu XMMWORD PTR [rsp+1808], xmm0
	movdqu XMMWORD PTR [rsp+1792], xmm0
	movdqu XMMWORD PTR [rsp+1776], xmm0
	movdqu XMMWORD PTR [rsp+1760], xmm0
	movdqu XMMWORD PTR [rsp+1744], xmm0
	movdqu XMMWORD PTR [rsp+1728], xmm0
	movdqu XMMWORD PTR [rsp+1712], xmm0
	movdqu XMMWORD PTR [rsp+1696], xmm0
	movdqu XMMWORD PTR [rsp+1680], xmm0
	movdqu XMMWORD PTR [rsp+1664], xmm0
	movdqu XMMWORD PTR [rsp+1648], xmm0
	movdqu XMMWORD PTR [rsp+1632], xmm0
	movdqu XMMWORD PTR [rsp+1616], xmm0
	movdqu XMMWORD PTR [rsp+1600], xmm0
	movdqu XMMWORD PTR [rsp+1584], xmm0
	movdqu XMMWORD PTR [rsp+1568], xmm0
	movdqu XMMWORD PTR [rsp+1552], xmm0
	movdqu XMMWORD PTR [rsp+1536], xmm0
	movdqu XMMWORD PTR [rsp+1520], xmm0
	movdqu XMMWORD PTR [rsp+1504], xmm0
	movdqu XMMWORD PTR [rsp+1488], xmm0
	movdqu XMMWORD PTR [rsp+1472], xmm0
	movdqu XMMWORD PTR [rsp+1456], xmm0
	movdqu XMMWORD PTR [rsp+1440], xmm0
	movdqu XMMWORD PTR [rsp+1424], xmm0
	movdqu XMMWORD PTR [rsp+1408], xmm0
	movdqu XMMWORD PTR [rsp+1392], xmm0
	movdqu XMMWORD PTR [rsp+1376], xmm0
	movdqu XMMWORD PTR [rsp+1360], xmm0
	movdqu XMMWORD PTR [rsp+1344], xmm0
	movdqu XMMWORD PTR [rsp+1328], xmm0
	movdqu XMMWORD PTR [rsp+1312], xmm0
	movdqu XMMWORD PTR [rsp+1296], xmm0
	movdqu XMMWORD PTR [rsp+1280], xmm0
	movdqu XMMWORD PTR [rsp+1264], xmm0
	movdqu XMMWORD PTR [rsp+1248], xmm0
	movdqu XMMWORD PTR [rsp+1232], xmm0
	movdqu XMMWORD PTR [rsp+1216], xmm0
	movdqu XMMWORD PTR [rsp+1200], xmm0
	movdqu XMMWORD PTR [rsp+1184], xmm0
	movdqu XMMWORD PTR [rsp+1168], xmm0
	movdqu XMMWORD PTR [rsp+1152], xmm0
	movdqu XMMWORD PTR [rsp+1136], xmm0
	movdqu XMMWORD PTR [rsp+1120], xmm0
	movdqu XMMWORD PTR [rsp+1104], xmm0
	movdqu XMMWORD PTR [rsp+1088], xmm0
	movdqu XMMWORD PTR [rsp+1072], xmm0
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
	lea rsp, [rsp+3176]
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
