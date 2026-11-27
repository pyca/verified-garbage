// The functions of `src/triple_des_ofb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_ofb:
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
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
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
	lea rsp, [rsp-8]
	lea rsp, [rsp-976]
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+976]
	lea rsp, [rsp+8]
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

vg_triple_des_ofb_final:
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
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
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
	lea rsp, [rsp-8]
	lea rsp, [rsp-976]
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+976]
	lea rsp, [rsp+8]
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
