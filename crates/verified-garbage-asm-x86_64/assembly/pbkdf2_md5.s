// The functions of `src/pbkdf2_md5.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_md5:
	lea rsp, [rsp-792]
	mov rax, QWORD PTR [rsp+800]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+128], rbx
	mov QWORD PTR [r8+136], rbp
	mov QWORD PTR [r8+144], r12
	mov QWORD PTR [r8+152], r13
	mov QWORD PTR [r8+160], r14
	mov QWORD PTR [r8+168], r15
	mov r15, r8
	mov QWORD PTR [r15+176], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+184], rax
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
	add rdi, 432
	call {vg_md5_init_core}
	mov rdi, r15
	add rdi, 432
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_md5_update_scratch}
	mov rdi, r15
	add rdi, 432
	mov rsi, rbp
	mov rdx, r15
	add rdx, 544
	mov rcx, r15
	call {vg_md5_finalize_scratch}
	mov rdx, r15
	add rdx, 544
	mov ecx, 16
21:
	mov rdi, r15
	add rdi, 192
	mov rsi, r15
	add rsi, 272
	mov r8, r15
	call {vg_hmac_md5_init_scratch}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+192]
	mov BYTE PTR [r15+r14*1+352], al
	add r14, 1
	cmp r14, 80
	jne 22b
	mov rdi, r15
	add rdi, 352
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_md5_update_scratch}
	mov rbp, r13
	mov r13, QWORD PTR [r15+176]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+352]
	mov BYTE PTR [r15+r14*1+432], al
	add r14, 1
	cmp r14, 80
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+560], eax
	mov rdi, r15
	add rdi, 432
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 560
	mov ecx, 4
	mov r8, r15
	call {vg_md5_update_scratch}
	mov rdi, r15
	add rdi, 432
	mov rsi, r15
	add rsi, 272
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 512
	mov r8, r15
	call {vg_hmac_md5_finalize_scratch}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+512]
	mov BYTE PTR [r15+r14*1+528], al
	add r14, 1
	cmp r14, 16
	jne 27b
	mov rdi, r15
	add rdi, 192
	mov rsi, r15
	add rsi, 512
	mov rdx, QWORD PTR [r15+184]
	mov rcx, r15
	add rcx, 528
	mov r8, r15
	call {vg_pbkdf2_hmac_md5_iterate}
	mov ecx, 16
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+528]
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
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+792]
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
	lea rsp, [rsp-816]
	mov QWORD PTR [rsp+808], r11
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
	lea rsp, [rsp+816]
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
