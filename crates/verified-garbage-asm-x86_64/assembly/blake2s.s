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
	lea rsp, [rsp-592]
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
	movdqu XMMWORD PTR [rsp+256], xmm0
	movdqu XMMWORD PTR [rsp+240], xmm0
	movdqu XMMWORD PTR [rsp+224], xmm0
	movdqu XMMWORD PTR [rsp+208], xmm0
	movdqu XMMWORD PTR [rsp+192], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
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
