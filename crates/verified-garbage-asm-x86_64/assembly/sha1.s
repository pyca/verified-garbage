// The functions of `src/sha1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_init:
	mov eax, 1732584193
	mov DWORD PTR [rdi], eax
	mov eax, -271733879
	mov DWORD PTR [rdi+4], eax
	mov eax, -1732584194
	mov DWORD PTR [rdi+8], eax
	mov eax, 271733878
	mov DWORD PTR [rdi+12], eax
	mov eax, -1009589776
	mov DWORD PTR [rdi+16], eax
	ret
	.p2align 6

vg_sha1_update:
	lea rsp, [rsp-168]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+112], rbx
	mov QWORD PTR [r8+120], rbp
	mov QWORD PTR [r8+128], r12
	mov QWORD PTR [r8+136], r13
	mov QWORD PTR [r8+144], r14
	mov QWORD PTR [r8+152], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+20], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+20], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 20
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+20], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+20], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 20
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+168]
	ret
	.p2align 6

vg_sha1_finalize:
	lea rsp, [rsp-168]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+112], rbx
	mov QWORD PTR [rcx+120], rbp
	mov QWORD PTR [rcx+128], r12
	mov QWORD PTR [rcx+136], r13
	mov QWORD PTR [rcx+144], r14
	mov QWORD PTR [rcx+152], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+20], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+20], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+20], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+76], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+20], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+68], xmm0
24:
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+168]
	ret
	.p2align 6

vg_sha1_digest:
	lea rsp, [rsp-280]
	mov rcx, rsp
	add rcx, 8
	add rcx, 96
	mov QWORD PTR [rcx+112], rbx
	mov QWORD PTR [rcx+120], rbp
	mov QWORD PTR [rcx+128], r12
	mov QWORD PTR [rcx+136], r13
	mov QWORD PTR [rcx+144], r14
	mov QWORD PTR [rcx+152], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 96
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	mov eax, 1732584193
	mov DWORD PTR [rdi], eax
	mov eax, -271733879
	mov DWORD PTR [rdi+4], eax
	mov eax, -1732584194
	mov DWORD PTR [rdi+8], eax
	mov eax, 271733878
	mov DWORD PTR [rdi+12], eax
	mov eax, -1009589776
	mov DWORD PTR [rdi+16], eax
	mov r14, r12
	shr r14, 6
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 6
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+20], xmm0
	movdqu XMMWORD PTR [rbx+36], xmm0
	movdqu XMMWORD PTR [rbx+52], xmm0
	movdqu XMMWORD PTR [rbx+68], xmm0
	mov r10, r12
	and r10, 63
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+20], xmm1
	add r13, 16
	add r11, 16
	sub r9, 1
	jne 24b
	jmp 23f
22:
23:
	mov rax, r10
	and rax, 15
	je 25f
	cmp r12, 8
	jb 27f
	cmp rax, 8
	jb 29f
	mov r8, QWORD PTR [r13]
	mov r9, QWORD PTR [r13+rax*1-8]
	mov ecx, 15
	sub rcx, rax
	shl rcx, 3
	shr r9, cl
	shr r9, 8
	mov rcx, rax
	sub rcx, 8
	shl rcx, 3
	mov edx, 128
	shl rdx, cl
	or r9, rdx
	movq xmm1, r8
	movq xmm2, r9
	punpcklqdq xmm1, xmm2
	movdqu XMMWORD PTR [rbx+r11*1+20], xmm1
	jmp 210f
29:
	mov r8, QWORD PTR [r13+rax*1-8]
	mov ecx, 8
	sub rcx, rax
	shl rcx, 3
	shr r8, cl
	mov rcx, rax
	shl rcx, 3
	mov r9d, 128
	shl r9, cl
	or r8, r9
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+20], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+20], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+20], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+20], xmm1
26:
	cmp r10, 56
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+20], xmm0
	movdqu XMMWORD PTR [rbx+36], xmm0
	movdqu XMMWORD PTR [rbx+52], xmm0
	movdqu XMMWORD PTR [rbx+68], xmm0
215:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	movdqu xmm0, XMMWORD PTR [rbx+68]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+68], xmm0
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+280]
	ret
	.p2align 6

vg_sha1_update_shani:
	lea rsp, [rsp-168]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+112], rbx
	mov QWORD PTR [r8+120], rbp
	mov QWORD PTR [r8+128], r12
	mov QWORD PTR [r8+136], r13
	mov QWORD PTR [r8+144], r14
	mov QWORD PTR [r8+152], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+20], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+20], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 20
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+20], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+20], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 20
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+168]
	ret
	.p2align 6

vg_sha1_finalize_shani:
	lea rsp, [rsp-168]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+112], rbx
	mov QWORD PTR [rcx+120], rbp
	mov QWORD PTR [rcx+128], r12
	mov QWORD PTR [rcx+136], r13
	mov QWORD PTR [rcx+144], r14
	mov QWORD PTR [rcx+152], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+20], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+20], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+20], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+76], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+20], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+68], xmm0
24:
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+168]
	ret
	.p2align 6

vg_sha1_digest_shani:
	lea rsp, [rsp-280]
	mov rcx, rsp
	add rcx, 8
	add rcx, 96
	mov QWORD PTR [rcx+112], rbx
	mov QWORD PTR [rcx+120], rbp
	mov QWORD PTR [rcx+128], r12
	mov QWORD PTR [rcx+136], r13
	mov QWORD PTR [rcx+144], r14
	mov QWORD PTR [rcx+152], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 96
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	mov eax, 1732584193
	mov DWORD PTR [rdi], eax
	mov eax, -271733879
	mov DWORD PTR [rdi+4], eax
	mov eax, -1732584194
	mov DWORD PTR [rdi+8], eax
	mov eax, 271733878
	mov DWORD PTR [rdi+12], eax
	mov eax, -1009589776
	mov DWORD PTR [rdi+16], eax
	mov r14, r12
	shr r14, 6
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 6
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+20], xmm0
	movdqu XMMWORD PTR [rbx+36], xmm0
	movdqu XMMWORD PTR [rbx+52], xmm0
	movdqu XMMWORD PTR [rbx+68], xmm0
	mov r10, r12
	and r10, 63
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+20], xmm1
	add r13, 16
	add r11, 16
	sub r9, 1
	jne 24b
	jmp 23f
22:
23:
	mov rax, r10
	and rax, 15
	je 25f
	cmp r12, 8
	jb 27f
	cmp rax, 8
	jb 29f
	mov r8, QWORD PTR [r13]
	mov r9, QWORD PTR [r13+rax*1-8]
	mov ecx, 15
	sub rcx, rax
	shl rcx, 3
	shr r9, cl
	shr r9, 8
	mov rcx, rax
	sub rcx, 8
	shl rcx, 3
	mov edx, 128
	shl rdx, cl
	or r9, rdx
	movq xmm1, r8
	movq xmm2, r9
	punpcklqdq xmm1, xmm2
	movdqu XMMWORD PTR [rbx+r11*1+20], xmm1
	jmp 210f
29:
	mov r8, QWORD PTR [r13+rax*1-8]
	mov ecx, 8
	sub rcx, rax
	shl rcx, 3
	shr r8, cl
	mov rcx, rax
	shl rcx, 3
	mov r9d, 128
	shl r9, cl
	or r8, r9
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+20], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+20], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+20], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+20], xmm1
26:
	cmp r10, 56
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+20], xmm0
	movdqu XMMWORD PTR [rbx+36], xmm0
	movdqu XMMWORD PTR [rbx+52], xmm0
	movdqu XMMWORD PTR [rbx+68], xmm0
215:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	movdqu xmm0, XMMWORD PTR [rbx+68]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+68], xmm0
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+280]
	ret
	.p2align 6
