// The functions of `src/blake2s.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2s_init:
	mov eax, -1150833019
	mov DWORD PTR [rdi+4], eax
	mov eax, 1013904242
	mov DWORD PTR [rdi+8], eax
	mov eax, -1521486534
	mov DWORD PTR [rdi+12], eax
	mov eax, 1359893119
	mov DWORD PTR [rdi+16], eax
	mov eax, -1694144372
	mov DWORD PTR [rdi+20], eax
	mov eax, 528734635
	mov DWORD PTR [rdi+24], eax
	mov eax, 1541459225
	mov DWORD PTR [rdi+28], eax
	mov eax, 1795745383
	mov r8, rcx
	ror r8d, 24
	xor eax, r8d
	xor eax, esi
	mov DWORD PTR [rdi], eax
	test rcx, rcx
	je 20f
	mov eax, 0
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov r8d, 0
22:
	movzx eax, BYTE PTR [rdx+r8*1]
	mov BYTE PTR [rdi+r8*1+32], al
	add r8, 1
	sub rcx, 1
	jne 22b
	jmp 21f
20:
21:
	xor eax, eax
	xor ecx, ecx
	xor r8d, r8d
	ret
	.p2align 6

vg_blake2s_update_avx:
	lea rsp, [rsp-584]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+512], rbx
	mov QWORD PTR [r8+520], rbp
	mov QWORD PTR [r8+528], r12
	mov QWORD PTR [r8+536], r13
	mov QWORD PTR [r8+544], r14
	mov QWORD PTR [r8+552], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 63
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	test r12, r12
	je 22f
	test r13, r13
	je 24f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 26f
	jmp 27f
26:
	mov rax, r12
27:
	sub r12, rax
	add r14, rax
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	test r12, r12
	je 211f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 32
	mov edx, 1
	mov rcx, r14
	mov r8d, 0
	mov r9, r15
	call {vg_blake2s_compress_avx}
	mov rbx, rdi
	mov r15, r9
	mov r13d, 0
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test r12, r12
	je 213f
	mov rax, r12
	sub rax, 1
	shr rax, 6
	test rax, rax
	je 215f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rax
	mov rcx, r14
	add rcx, 64
	mov r8d, 0
	mov r9, r15
	call {vg_blake2s_compress_avx}
	mov rbx, rdi
	mov r15, r9
	mov rax, r12
	sub rax, 1
	and rax, 63
	add rax, 1
	sub r12, rax
	add rbp, r12
	add r14, r12
	mov r12, rax
	jmp 216f
215:
216:
	mov rax, r12
	add r14, rax
	mov r12d, 0
217:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
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
	je 218f
	xor r11d, r11d
	lea rsp, [rsp-592]
	mov QWORD PTR [rsp+584], r11
	movdqu XMMWORD PTR [rsp+568], xmm0
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
	lea rsp, [rsp+592]
	jmp 219f
218:
	xor r11d, r11d
	lea rsp, [rsp-592]
	mov QWORD PTR [rsp+584], r11
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
	lea rsp, [rsp+592]
219:
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	ret
	.p2align 6

vg_blake2s_finalize_avx:
	lea rsp, [rsp-584]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+512], rbx
	mov QWORD PTR [rcx+520], rbp
	mov QWORD PTR [rcx+528], r12
	mov QWORD PTR [rcx+536], r13
	mov QWORD PTR [rcx+544], r14
	mov QWORD PTR [rcx+552], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 63
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	mov r9d, 0
	mov eax, 64
	sub rax, r13
	je 22f
24:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 24b
	jmp 23f
22:
23:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 32
	mov edx, 1
	mov rcx, r14
	mov r8d, 1
	mov r9, r15
	call {vg_blake2s_compress_avx}
	mov rbx, rdi
	mov r15, r9
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
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
	lea rsp, [rsp-592]
	lea rsp, [rsp+592]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	ret
	.p2align 6

vg_blake2s_update:
	lea rsp, [rsp-584]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+512], rbx
	mov QWORD PTR [r8+520], rbp
	mov QWORD PTR [r8+528], r12
	mov QWORD PTR [r8+536], r13
	mov QWORD PTR [r8+544], r14
	mov QWORD PTR [r8+552], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 63
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	test r12, r12
	je 22f
	test r13, r13
	je 24f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 26f
	jmp 27f
26:
	mov rax, r12
27:
	sub r12, rax
	add r14, rax
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	test r12, r12
	je 211f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 32
	mov edx, 1
	mov rcx, r14
	mov r8d, 0
	mov r9, r15
	call {vg_blake2s_compress}
	mov rbx, rdi
	mov r15, r9
	mov r13d, 0
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test r12, r12
	je 213f
	mov rax, r12
	sub rax, 1
	shr rax, 6
	test rax, rax
	je 215f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rax
	mov rcx, r14
	add rcx, 64
	mov r8d, 0
	mov r9, r15
	call {vg_blake2s_compress}
	mov rbx, rdi
	mov r15, r9
	mov rax, r12
	sub rax, 1
	and rax, 63
	add rax, 1
	sub r12, rax
	add rbp, r12
	add r14, r12
	mov r12, rax
	jmp 216f
215:
216:
	mov rax, r12
	add r14, rax
	mov r12d, 0
217:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	pxor xmm0, xmm0
	xor r11d, r11d
	lea rsp, [rsp-592]
	mov QWORD PTR [rsp+584], r11
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
	lea rsp, [rsp+592]
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

vg_blake2s_finalize:
	lea rsp, [rsp-584]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+512], rbx
	mov QWORD PTR [rcx+520], rbp
	mov QWORD PTR [rcx+528], r12
	mov QWORD PTR [rcx+536], r13
	mov QWORD PTR [rcx+544], r14
	mov QWORD PTR [rcx+552], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 63
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	mov r9d, 0
	mov eax, 64
	sub rax, r13
	je 22f
24:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 24b
	jmp 23f
22:
23:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 32
	mov edx, 1
	mov rcx, r14
	mov r8d, 1
	mov r9, r15
	call {vg_blake2s_compress}
	mov rbx, rdi
	mov r15, r9
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	pxor xmm0, xmm0
	xor r11d, r11d
	lea rsp, [rsp-592]
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+592]
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
