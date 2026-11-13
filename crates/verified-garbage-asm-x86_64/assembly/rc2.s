// The functions of `src/rc2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	lea rsp, [rsp-592]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov eax, 1
	mov r10, rsi
	sub r10, 1
	cmp r10, 128
	jae 20f
	mov eax, 2
	mov r10, rdx
	sub r10, 1
	cmp r10, 1024
	jae 22f
	mov eax, 3
	cmp r8, 8
	jne 24f
	mov eax, 0
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	jmp 21f
20:
21:
	test rax, rax
	jne 26f
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r9+128], rax
	mov rcx, r9
	mov r8, QWORD PTR [rsp+8]
	call {vg_rc2_expand_key}
	mov eax, 0
	jmp 27f
26:
27:
	mov r11d, 0
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
	lea rsp, [rsp+592]
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
	lea rsp, [rsp-600]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+600]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6
