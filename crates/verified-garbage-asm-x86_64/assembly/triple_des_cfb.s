// The functions of `src/triple_des_cfb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_cfb64_encrypt:
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
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9+512], rbp
	test r13, r13
	je 20f
22:
	mov rdi, r9
	add rdi, 520
	mov rsi, r9
	add rsi, 512
	mov rdx, r9
	call {vg_triple_des_encrypt_block}
	mov r9, rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9+512]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r9+512], rax
	add r12, 8
	sub r13, 1
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9+512]
	mov QWORD PTR [rax], rbp
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
	movdqu XMMWORD PTR [rsp+8], xmm0
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

vg_triple_des_cfb64_encrypt_final:
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
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9+512], rbp
	test r13, r13
	je 20f
22:
	mov rdi, r9
	add rdi, 520
	mov rsi, r9
	add rsi, 512
	mov rdx, r9
	call {vg_triple_des_encrypt_block}
	mov r9, rdx
	cmp r13, 8
	jb 23f
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9+512]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r9+512], rax
	add r12, 8
	sub r13, 8
	jmp 24f
23:
	mov rax, r9
	add rax, 512
25:
	movzx r10d, BYTE PTR [rax]
	movzx ecx, BYTE PTR [r12]
	xor rcx, r10
	mov BYTE PTR [r12], cl
	add rax, 1
	add r12, 1
	sub r13, 1
	jne 25b
24:
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9+512]
	mov QWORD PTR [rax], rbp
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
	movdqu XMMWORD PTR [rsp+8], xmm0
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

vg_triple_des_cfb64_decrypt_final:
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
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9+512], rbp
	test r13, r13
	je 20f
22:
	mov rdi, r9
	add rdi, 520
	mov rsi, r9
	add rsi, 512
	mov rdx, r9
	call {vg_triple_des_encrypt_block}
	mov r9, rdx
	cmp r13, 8
	jb 23f
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9+512]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r9+512]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [r9+512], rax
	add r12, 8
	sub r13, 8
	jmp 24f
23:
	mov rax, r9
	add rax, 512
25:
	movzx r10d, BYTE PTR [rax]
	movzx ecx, BYTE PTR [r12]
	xor rcx, r10
	mov BYTE PTR [r12], cl
	add rax, 1
	add r12, 1
	sub r13, 1
	jne 25b
24:
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9+512]
	mov QWORD PTR [rax], rbp
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
	movdqu XMMWORD PTR [rsp+8], xmm0
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

vg_triple_des_cfb64_decrypt_avx512:
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
	mov rax, r12
	mov rbx, r9
	mov rcx, r10
28:
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [rax], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 28b
	mov rdi, r15
	mov rsi, r12
	mov rdx, r10
	call {vg_triple_des_ecb_encrypt_avx512_core}
	mov r9, r13
	movabs rcx, 256
	cmp r14, 256
	jb 29f
	jmp 210f
29:
	mov rcx, r14
210:
	mov rbx, r12
	mov r10, rcx
	mov rax, r9
	add rax, 8
211:
	mov rbp, QWORD PTR [rbx]
	xor rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 211b
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
	lea rsp, [rsp-3176]
	vmovdqu YMMWORD PTR [rsp+3144], ymm0
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

vg_triple_des_cfb64_decrypt_avx2:
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
	mov rax, r12
	mov rbx, r9
	mov rcx, r10
28:
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [rax], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 28b
	mov rdi, r15
	mov rsi, r12
	mov rdx, r10
	call {vg_triple_des_ecb_encrypt_avx2_core}
	mov r9, r13
	movabs rcx, 256
	cmp r14, 256
	jb 29f
	jmp 210f
29:
	mov rcx, r14
210:
	mov rbx, r12
	mov r10, rcx
	mov rax, r9
	add rax, 8
211:
	mov rbp, QWORD PTR [rbx]
	xor rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 211b
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
	lea rsp, [rsp-3176]
	vmovdqu YMMWORD PTR [rsp+3144], ymm0
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

vg_triple_des_cfb64_decrypt:
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
	mov rax, r12
	mov rbx, r9
	mov rcx, r10
28:
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [rax], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 28b
	mov rdi, r15
	mov rsi, r12
	mov rdx, r10
	call {vg_triple_des_ecb_encrypt_core}
	mov r9, r13
	movabs rcx, 256
	cmp r14, 256
	jb 29f
	jmp 210f
29:
	mov rcx, r14
210:
	mov rbx, r12
	mov r10, rcx
	mov rax, r9
	add rax, 8
211:
	mov rbp, QWORD PTR [rbx]
	xor rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 211b
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
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
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
