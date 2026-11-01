// The functions of `src/sha512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha384_init:
	movabs rax, -3766243637369397544
	mov QWORD PTR [rdi], rax
	movabs rax, 7105036623409894663
	mov QWORD PTR [rdi+8], rax
	movabs rax, -7973340178411365097
	mov QWORD PTR [rdi+16], rax
	movabs rax, 1526699215303891257
	mov QWORD PTR [rdi+24], rax
	movabs rax, 7436329637833083697
	mov QWORD PTR [rdi+32], rax
	movabs rax, -8163818279084223215
	mov QWORD PTR [rdi+40], rax
	movabs rax, -2662702644619276377
	mov QWORD PTR [rdi+48], rax
	movabs rax, 5167115440072839076
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6

vg_sha512_init:
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6

vg_sha512_224_init:
	movabs rax, -8341449602262348382
	mov QWORD PTR [rdi], rax
	movabs rax, 8350123849800275158
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2160240930085379202
	mov QWORD PTR [rdi+16], rax
	movabs rax, 7466358040605728719
	mov QWORD PTR [rdi+24], rax
	movabs rax, 1111592415079452072
	mov QWORD PTR [rdi+32], rax
	movabs rax, 8638871050018654530
	mov QWORD PTR [rdi+40], rax
	movabs rax, 4583966954114332360
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1230299281376055969
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6

vg_sha512_256_init:
	movabs rax, 2463787394917988140
	mov QWORD PTR [rdi], rax
	movabs rax, -6965556091613846334
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2563595384472711505
	mov QWORD PTR [rdi+16], rax
	movabs rax, -7622211418569250115
	mov QWORD PTR [rdi+24], rax
	movabs rax, -7626776825740460061
	mov QWORD PTR [rdi+32], rax
	movabs rax, -4729309413028513390
	mov QWORD PTR [rdi+40], rax
	movabs rax, 3098927326965381290
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1060366662362279074
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6

vg_sha384_finalize:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha384_digest:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -3766243637369397544
	mov QWORD PTR [rdi], rax
	movabs rax, 7105036623409894663
	mov QWORD PTR [rdi+8], rax
	movabs rax, -7973340178411365097
	mov QWORD PTR [rdi+16], rax
	movabs rax, 1526699215303891257
	mov QWORD PTR [rdi+24], rax
	movabs rax, 7436329637833083697
	mov QWORD PTR [rdi+32], rax
	movabs rax, -8163818279084223215
	mov QWORD PTR [rdi+40], rax
	movabs rax, -2662702644619276377
	mov QWORD PTR [rdi+48], rax
	movabs rax, 5167115440072839076
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha384_finalize_avx2:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha384_digest_avx2:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -3766243637369397544
	mov QWORD PTR [rdi], rax
	movabs rax, 7105036623409894663
	mov QWORD PTR [rdi+8], rax
	movabs rax, -7973340178411365097
	mov QWORD PTR [rdi+16], rax
	movabs rax, 1526699215303891257
	mov QWORD PTR [rdi+24], rax
	movabs rax, 7436329637833083697
	mov QWORD PTR [rdi+32], rax
	movabs rax, -8163818279084223215
	mov QWORD PTR [rdi+40], rax
	movabs rax, -2662702644619276377
	mov QWORD PTR [rdi+48], rax
	movabs rax, 5167115440072839076
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha384_finalize_shani:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha384_digest_shani:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -3766243637369397544
	mov QWORD PTR [rdi], rax
	movabs rax, 7105036623409894663
	mov QWORD PTR [rdi+8], rax
	movabs rax, -7973340178411365097
	mov QWORD PTR [rdi+16], rax
	movabs rax, 1526699215303891257
	mov QWORD PTR [rdi+24], rax
	movabs rax, 7436329637833083697
	mov QWORD PTR [rdi+32], rax
	movabs rax, -8163818279084223215
	mov QWORD PTR [rdi+40], rax
	movabs rax, -2662702644619276377
	mov QWORD PTR [rdi+48], rax
	movabs rax, 5167115440072839076
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_update:
	lea rsp, [rsp-1384]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_finalize:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_digest:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_update_avx2:
	lea rsp, [rsp-1384]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_finalize_avx2:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_digest_avx2:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_update_shani:
	lea rsp, [rsp-1384]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_finalize_shani:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_digest_shani:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_224_finalize:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_224_digest:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -8341449602262348382
	mov QWORD PTR [rdi], rax
	movabs rax, 8350123849800275158
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2160240930085379202
	mov QWORD PTR [rdi+16], rax
	movabs rax, 7466358040605728719
	mov QWORD PTR [rdi+24], rax
	movabs rax, 1111592415079452072
	mov QWORD PTR [rdi+32], rax
	movabs rax, 8638871050018654530
	mov QWORD PTR [rdi+40], rax
	movabs rax, 4583966954114332360
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1230299281376055969
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_224_finalize_avx2:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_224_digest_avx2:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -8341449602262348382
	mov QWORD PTR [rdi], rax
	movabs rax, 8350123849800275158
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2160240930085379202
	mov QWORD PTR [rdi+16], rax
	movabs rax, 7466358040605728719
	mov QWORD PTR [rdi+24], rax
	movabs rax, 1111592415079452072
	mov QWORD PTR [rdi+32], rax
	movabs rax, 8638871050018654530
	mov QWORD PTR [rdi+40], rax
	movabs rax, 4583966954114332360
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1230299281376055969
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_224_finalize_shani:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_224_digest_shani:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, -8341449602262348382
	mov QWORD PTR [rdi], rax
	movabs rax, 8350123849800275158
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2160240930085379202
	mov QWORD PTR [rdi+16], rax
	movabs rax, 7466358040605728719
	mov QWORD PTR [rdi+24], rax
	movabs rax, 1111592415079452072
	mov QWORD PTR [rdi+32], rax
	movabs rax, 8638871050018654530
	mov QWORD PTR [rdi+40], rax
	movabs rax, 4583966954114332360
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1230299281376055969
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_256_finalize:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_256_digest:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 2463787394917988140
	mov QWORD PTR [rdi], rax
	movabs rax, -6965556091613846334
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2563595384472711505
	mov QWORD PTR [rdi+16], rax
	movabs rax, -7622211418569250115
	mov QWORD PTR [rdi+24], rax
	movabs rax, -7626776825740460061
	mov QWORD PTR [rdi+32], rax
	movabs rax, -4729309413028513390
	mov QWORD PTR [rdi+40], rax
	movabs rax, 3098927326965381290
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1060366662362279074
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_256_finalize_avx2:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_256_digest_avx2:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 2463787394917988140
	mov QWORD PTR [rdi], rax
	movabs rax, -6965556091613846334
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2563595384472711505
	mov QWORD PTR [rdi+16], rax
	movabs rax, -7622211418569250115
	mov QWORD PTR [rdi+24], rax
	movabs rax, -7626776825740460061
	mov QWORD PTR [rdi+32], rax
	movabs rax, -4729309413028513390
	mov QWORD PTR [rdi+40], rax
	movabs rax, 3098927326965381290
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1060366662362279074
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6

vg_sha512_256_finalize_shani:
	lea rsp, [rsp-1384]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
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
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1384]
	ret
	.p2align 6

vg_sha512_256_digest_shani:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 2463787394917988140
	mov QWORD PTR [rdi], rax
	movabs rax, -6965556091613846334
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2563595384472711505
	mov QWORD PTR [rdi+16], rax
	movabs rax, -7622211418569250115
	mov QWORD PTR [rdi+24], rax
	movabs rax, -7626776825740460061
	mov QWORD PTR [rdi+32], rax
	movabs rax, -4729309413028513390
	mov QWORD PTR [rdi+40], rax
	movabs rax, 3098927326965381290
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1060366662362279074
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
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
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov BYTE PTR [rbx+r11*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov BYTE PTR [rbx+r11*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	movdqu XMMWORD PTR [rbx+r11*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6
