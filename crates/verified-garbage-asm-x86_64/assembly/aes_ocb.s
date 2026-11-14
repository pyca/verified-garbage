// The functions of `src/aes_ocb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ocb_init_vaes:
	lea rsp, [rsp-32]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov rbx, rdx
	mov rbp, rsi
	shr rbp, 2
	add rbp, 6
	mov r12, rcx
	add rcx, 512
	call {vg_aes_expand_key_scratch_aesni}
	xor rax, rax
	mov QWORD PTR [rbx+240], rax
	mov QWORD PTR [rbx+248], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 240
	mov rcx, 1
	mov r8, r12
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rbx, QWORD PTR [r12]
	mov rbp, QWORD PTR [r12+8]
	mov r12, QWORD PTR [r12+16]
	lea rsp, [rsp+32]
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
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	lea rsp, [rsp+40]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	ret
	.p2align 6

vg_aes_ocb_seal_vaes:
	lea rsp, [rsp-3632]
	mov rax, QWORD PTR [rsp+3640]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3648]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3656]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+3664]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	mov QWORD PTR [r15+2560], rax
	mov QWORD PTR [r15+2568], rdx
	mov r9, QWORD PTR [r15+216]
	mov rax, QWORD PTR [r15+248]
	or r9, rax
	shr r9, 5
	mov r10, r15
	add r10, 2560
	mov r11, 1
	movabs rsi, 157587932685088877
	test r9, r9
	je 20f
22:
	add r11, r11
	mov rax, r11
	mul rsi
	shr rax, 58
	ror rax, 60
	add rax, r15
	mov rdi, rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov rdx, QWORD PTR [r10+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	bswap rdx
	mov QWORD PTR [rdi+2568], rdx
	mov r10, rdi
	add r10, 2560
	shr r9, 1
	test r9, r9
	jne 22b
	jmp 21f
20:
21:
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
23:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 23b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	xor rax, rax
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rax
	xor rax, rax
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rax
	mov rbx, QWORD PTR [r15+240]
	mov rax, QWORD PTR [r15+248]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+112], rcx
	shr rax, 4
	mov QWORD PTR [r15+248], rax
	mov rbp, 1
	test rax, rax
	je 24f
26:
	mov r12, QWORD PTR [r15+248]
	cmp r12, 8
	jb 27f
	mov r12, 8
	jmp 28f
27:
28:
	mov r13, 0
	mov rsi, r15
	add rsi, 384
29:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [rcx+2560]
	xor rdx, QWORD PTR [rcx+2568]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [rbx]
	mov rdx, QWORD PTR [rbx+8]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rdx
	add rsi, 16
	add rbx, 16
	add rbp, 1
	add r13, 1
	cmp r13, r12
	jne 29b
	mov rdx, r15
	add rdx, 384
	mov rcx, r12
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov r13, 0
	mov rsi, r15
	add rsi, 384
210:
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [rsi]
	xor rdx, QWORD PTR [rsi+8]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	add rsi, 16
	add r13, 1
	cmp r13, r12
	jne 210b
	mov rax, QWORD PTR [r15+248]
	sub rax, r12
	mov QWORD PTR [r15+248], rax
	jne 26b
	jmp 25f
24:
25:
	mov r12, QWORD PTR [r15+112]
	test r12, r12
	je 211f
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	xor rax, rax
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rax
	mov rsi, r15
	add rsi, 384
	mov rcx, 0
213:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 213b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+384]
	mov rdx, QWORD PTR [r15+392]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rdx
	mov rdx, r15
	add rdx, 384
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [r15+384]
	xor rdx, QWORD PTR [r15+392]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	jmp 212f
211:
212:
	mov r13, QWORD PTR [r15+216]
	shr r13, 4
	test r13, r13
	je 214f
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 216f
218:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 218b
	jmp 217f
216:
217:
	test r12, r12
	je 219f
221:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 221b
	jmp 220f
219:
220:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	mov rdx, QWORD PTR [r15+208]
	mov rcx, r13
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, QWORD PTR [r15+272]
	mov rdx, QWORD PTR [r15+280]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 222f
224:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 224b
	jmp 223f
222:
223:
	test r12, r12
	je 225f
227:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 227b
	jmp 226f
225:
226:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+208]
	mov rax, QWORD PTR [r15+216]
	mov r12, rax
	and r12, 15
	sub rax, r12
	add rbx, rax
	test r12, r12
	je 228f
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
230:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 230b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+128]
	xor rdx, QWORD PTR [r15+136]
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rdx
	mov rcx, 0
231:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 231b
	jmp 229f
228:
229:
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+16]
	xor rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+64]
	xor rdx, QWORD PTR [r15+72]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rdx
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	xor rax, QWORD PTR [r15+48]
	xor rdx, QWORD PTR [r15+56]
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rdx
	mov rbx, r15
	mov rsi, QWORD PTR [r15+304]
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
232:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 232b
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+3632]
	ret
	.p2align 6

vg_aes_ocb_open_vaes:
	lea rsp, [rsp-3632]
	mov rax, QWORD PTR [rsp+3640]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3648]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3656]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+3664]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	mov QWORD PTR [r15+2560], rax
	mov QWORD PTR [r15+2568], rdx
	mov r9, QWORD PTR [r15+216]
	mov rax, QWORD PTR [r15+248]
	or r9, rax
	shr r9, 5
	mov r10, r15
	add r10, 2560
	mov r11, 1
	movabs rsi, 157587932685088877
	test r9, r9
	je 20f
22:
	add r11, r11
	mov rax, r11
	mul rsi
	shr rax, 58
	ror rax, 60
	add rax, r15
	mov rdi, rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov rdx, QWORD PTR [r10+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	bswap rdx
	mov QWORD PTR [rdi+2568], rdx
	mov r10, rdi
	add r10, 2560
	shr r9, 1
	test r9, r9
	jne 22b
	jmp 21f
20:
21:
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
23:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 23b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	xor rax, rax
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rax
	xor rax, rax
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rax
	mov rbx, QWORD PTR [r15+240]
	mov rax, QWORD PTR [r15+248]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+112], rcx
	shr rax, 4
	mov QWORD PTR [r15+248], rax
	mov rbp, 1
	test rax, rax
	je 24f
26:
	mov r12, QWORD PTR [r15+248]
	cmp r12, 8
	jb 27f
	mov r12, 8
	jmp 28f
27:
28:
	mov r13, 0
	mov rsi, r15
	add rsi, 384
29:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [rcx+2560]
	xor rdx, QWORD PTR [rcx+2568]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [rbx]
	mov rdx, QWORD PTR [rbx+8]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rdx
	add rsi, 16
	add rbx, 16
	add rbp, 1
	add r13, 1
	cmp r13, r12
	jne 29b
	mov rdx, r15
	add rdx, 384
	mov rcx, r12
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov r13, 0
	mov rsi, r15
	add rsi, 384
210:
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [rsi]
	xor rdx, QWORD PTR [rsi+8]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	add rsi, 16
	add r13, 1
	cmp r13, r12
	jne 210b
	mov rax, QWORD PTR [r15+248]
	sub rax, r12
	mov QWORD PTR [r15+248], rax
	jne 26b
	jmp 25f
24:
25:
	mov r12, QWORD PTR [r15+112]
	test r12, r12
	je 211f
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	xor rax, rax
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rax
	mov rsi, r15
	add rsi, 384
	mov rcx, 0
213:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 213b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+384]
	mov rdx, QWORD PTR [r15+392]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rdx
	mov rdx, r15
	add rdx, 384
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [r15+384]
	xor rdx, QWORD PTR [r15+392]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	jmp 212f
211:
212:
	mov r13, QWORD PTR [r15+216]
	shr r13, 4
	test r13, r13
	je 214f
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 216f
218:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 218b
	jmp 217f
216:
217:
	test r12, r12
	je 219f
221:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 221b
	jmp 220f
219:
220:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	mov rdx, QWORD PTR [r15+208]
	mov rcx, r13
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_decrypt_blocks_vaes}
	mov rax, QWORD PTR [r15+272]
	mov rdx, QWORD PTR [r15+280]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 222f
224:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 224b
	jmp 223f
222:
223:
	test r12, r12
	je 225f
227:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 227b
	jmp 226f
225:
226:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+208]
	mov rax, QWORD PTR [r15+216]
	mov r12, rax
	and r12, 15
	sub rax, r12
	add rbx, rax
	test r12, r12
	je 228f
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, 0
230:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 230b
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
231:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 231b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+128]
	xor rdx, QWORD PTR [r15+136]
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rdx
	jmp 229f
228:
229:
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+16]
	xor rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+64]
	xor rdx, QWORD PTR [r15+72]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rdx
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	xor rax, QWORD PTR [r15+48]
	xor rdx, QWORD PTR [r15+56]
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rdx
	mov rbx, QWORD PTR [r15+304]
	mov rsi, r15
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
232:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 232b
	xor rdx, rdx
	mov rcx, 0
	mov r12, QWORD PTR [r15+224]
233:
	movzx eax, BYTE PTR [r15+rcx*1]
	movzx r8d, BYTE PTR [r15+rcx*1+128]
	xor rax, r8
	or rdx, rax
	add rcx, 1
	cmp rcx, r12
	jne 233b
	sub rdx, 1
	shr rdx, 63
	mov QWORD PTR [r15], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, QWORD PTR [r15+216]
	xor rdx, rdx
	sub rdx, QWORD PTR [r15]
	movq xmm6, rdx
	punpcklqdq xmm6, xmm6
	mov rcx, 0
	mov r8, r12
	shr r8, 4
	test r8, r8
	je 234f
236:
	movdqu xmm7, XMMWORD PTR [rbx+rcx*1]
	pand xmm7, xmm6
	movdqu XMMWORD PTR [rbx+rcx*1], xmm7
	add rcx, 16
	sub r8, 1
	jne 236b
	jmp 235f
234:
235:
	cmp rcx, r12
	je 237f
239:
	movzx eax, BYTE PTR [rbx+rcx*1]
	and rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 239b
	jmp 238f
237:
238:
	mov rax, QWORD PTR [r15]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+3632]
	ret
	.p2align 6

vg_aes_ocb_init_aesni:
	lea rsp, [rsp-32]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov rbx, rdx
	mov rbp, rsi
	shr rbp, 2
	add rbp, 6
	mov r12, rcx
	add rcx, 512
	call {vg_aes_expand_key_scratch_aesni}
	xor rax, rax
	mov QWORD PTR [rbx+240], rax
	mov QWORD PTR [rbx+248], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 240
	mov rcx, 1
	mov r8, r12
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rbx, QWORD PTR [r12]
	mov rbp, QWORD PTR [r12+8]
	mov r12, QWORD PTR [r12+16]
	lea rsp, [rsp+32]
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
	lea rsp, [rsp-40]
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+40]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	ret
	.p2align 6

vg_aes_ocb_seal_aesni:
	lea rsp, [rsp-3632]
	mov rax, QWORD PTR [rsp+3640]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3648]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3656]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+3664]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	mov QWORD PTR [r15+2560], rax
	mov QWORD PTR [r15+2568], rdx
	mov r9, QWORD PTR [r15+216]
	mov rax, QWORD PTR [r15+248]
	or r9, rax
	shr r9, 5
	mov r10, r15
	add r10, 2560
	mov r11, 1
	movabs rsi, 157587932685088877
	test r9, r9
	je 20f
22:
	add r11, r11
	mov rax, r11
	mul rsi
	shr rax, 58
	ror rax, 60
	add rax, r15
	mov rdi, rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov rdx, QWORD PTR [r10+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	bswap rdx
	mov QWORD PTR [rdi+2568], rdx
	mov r10, rdi
	add r10, 2560
	shr r9, 1
	test r9, r9
	jne 22b
	jmp 21f
20:
21:
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
23:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 23b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	xor rax, rax
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rax
	xor rax, rax
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rax
	mov rbx, QWORD PTR [r15+240]
	mov rax, QWORD PTR [r15+248]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+112], rcx
	shr rax, 4
	mov QWORD PTR [r15+248], rax
	mov rbp, 1
	test rax, rax
	je 24f
26:
	mov r12, QWORD PTR [r15+248]
	cmp r12, 8
	jb 27f
	mov r12, 8
	jmp 28f
27:
28:
	mov r13, 0
	mov rsi, r15
	add rsi, 384
29:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [rcx+2560]
	xor rdx, QWORD PTR [rcx+2568]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [rbx]
	mov rdx, QWORD PTR [rbx+8]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rdx
	add rsi, 16
	add rbx, 16
	add rbp, 1
	add r13, 1
	cmp r13, r12
	jne 29b
	mov rdx, r15
	add rdx, 384
	mov rcx, r12
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov r13, 0
	mov rsi, r15
	add rsi, 384
210:
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [rsi]
	xor rdx, QWORD PTR [rsi+8]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	add rsi, 16
	add r13, 1
	cmp r13, r12
	jne 210b
	mov rax, QWORD PTR [r15+248]
	sub rax, r12
	mov QWORD PTR [r15+248], rax
	jne 26b
	jmp 25f
24:
25:
	mov r12, QWORD PTR [r15+112]
	test r12, r12
	je 211f
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	xor rax, rax
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rax
	mov rsi, r15
	add rsi, 384
	mov rcx, 0
213:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 213b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+384]
	mov rdx, QWORD PTR [r15+392]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rdx
	mov rdx, r15
	add rdx, 384
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [r15+384]
	xor rdx, QWORD PTR [r15+392]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	jmp 212f
211:
212:
	mov r13, QWORD PTR [r15+216]
	shr r13, 4
	test r13, r13
	je 214f
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 216f
218:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 218b
	jmp 217f
216:
217:
	test r12, r12
	je 219f
221:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 221b
	jmp 220f
219:
220:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	mov rdx, QWORD PTR [r15+208]
	mov rcx, r13
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r15+272]
	mov rdx, QWORD PTR [r15+280]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 222f
224:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 224b
	jmp 223f
222:
223:
	test r12, r12
	je 225f
227:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 227b
	jmp 226f
225:
226:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+208]
	mov rax, QWORD PTR [r15+216]
	mov r12, rax
	and r12, 15
	sub rax, r12
	add rbx, rax
	test r12, r12
	je 228f
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
230:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 230b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+128]
	xor rdx, QWORD PTR [r15+136]
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rdx
	mov rcx, 0
231:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 231b
	jmp 229f
228:
229:
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+16]
	xor rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+64]
	xor rdx, QWORD PTR [r15+72]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rdx
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	xor rax, QWORD PTR [r15+48]
	xor rdx, QWORD PTR [r15+56]
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rdx
	mov rbx, r15
	mov rsi, QWORD PTR [r15+304]
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
232:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 232b
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+3632]
	ret
	.p2align 6

vg_aes_ocb_open_aesni:
	lea rsp, [rsp-3632]
	mov rax, QWORD PTR [rsp+3640]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3648]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3656]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+3664]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	mov QWORD PTR [r15+2560], rax
	mov QWORD PTR [r15+2568], rdx
	mov r9, QWORD PTR [r15+216]
	mov rax, QWORD PTR [r15+248]
	or r9, rax
	shr r9, 5
	mov r10, r15
	add r10, 2560
	mov r11, 1
	movabs rsi, 157587932685088877
	test r9, r9
	je 20f
22:
	add r11, r11
	mov rax, r11
	mul rsi
	shr rax, 58
	ror rax, 60
	add rax, r15
	mov rdi, rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov rdx, QWORD PTR [r10+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	bswap rdx
	mov QWORD PTR [rdi+2568], rdx
	mov r10, rdi
	add r10, 2560
	shr r9, 1
	test r9, r9
	jne 22b
	jmp 21f
20:
21:
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
23:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 23b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	xor rax, rax
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rax
	xor rax, rax
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rax
	mov rbx, QWORD PTR [r15+240]
	mov rax, QWORD PTR [r15+248]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+112], rcx
	shr rax, 4
	mov QWORD PTR [r15+248], rax
	mov rbp, 1
	test rax, rax
	je 24f
26:
	mov r12, QWORD PTR [r15+248]
	cmp r12, 8
	jb 27f
	mov r12, 8
	jmp 28f
27:
28:
	mov r13, 0
	mov rsi, r15
	add rsi, 384
29:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [rcx+2560]
	xor rdx, QWORD PTR [rcx+2568]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [rbx]
	mov rdx, QWORD PTR [rbx+8]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rdx
	add rsi, 16
	add rbx, 16
	add rbp, 1
	add r13, 1
	cmp r13, r12
	jne 29b
	mov rdx, r15
	add rdx, 384
	mov rcx, r12
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov r13, 0
	mov rsi, r15
	add rsi, 384
210:
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [rsi]
	xor rdx, QWORD PTR [rsi+8]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	add rsi, 16
	add r13, 1
	cmp r13, r12
	jne 210b
	mov rax, QWORD PTR [r15+248]
	sub rax, r12
	mov QWORD PTR [r15+248], rax
	jne 26b
	jmp 25f
24:
25:
	mov r12, QWORD PTR [r15+112]
	test r12, r12
	je 211f
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	xor rax, rax
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rax
	mov rsi, r15
	add rsi, 384
	mov rcx, 0
213:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 213b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+384]
	mov rdx, QWORD PTR [r15+392]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rdx
	mov rdx, r15
	add rdx, 384
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [r15+384]
	xor rdx, QWORD PTR [r15+392]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	jmp 212f
211:
212:
	mov r13, QWORD PTR [r15+216]
	shr r13, 4
	test r13, r13
	je 214f
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 216f
218:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 218b
	jmp 217f
216:
217:
	test r12, r12
	je 219f
221:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 221b
	jmp 220f
219:
220:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	mov rdx, QWORD PTR [r15+208]
	mov rcx, r13
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_decrypt_blocks_aesni}
	mov rax, QWORD PTR [r15+272]
	mov rdx, QWORD PTR [r15+280]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 222f
224:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 224b
	jmp 223f
222:
223:
	test r12, r12
	je 225f
227:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 227b
	jmp 226f
225:
226:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+208]
	mov rax, QWORD PTR [r15+216]
	mov r12, rax
	and r12, 15
	sub rax, r12
	add rbx, rax
	test r12, r12
	je 228f
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, 0
230:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 230b
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
231:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 231b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+128]
	xor rdx, QWORD PTR [r15+136]
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rdx
	jmp 229f
228:
229:
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+16]
	xor rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+64]
	xor rdx, QWORD PTR [r15+72]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rdx
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	xor rax, QWORD PTR [r15+48]
	xor rdx, QWORD PTR [r15+56]
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rdx
	mov rbx, QWORD PTR [r15+304]
	mov rsi, r15
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
232:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 232b
	xor rdx, rdx
	mov rcx, 0
	mov r12, QWORD PTR [r15+224]
233:
	movzx eax, BYTE PTR [r15+rcx*1]
	movzx r8d, BYTE PTR [r15+rcx*1+128]
	xor rax, r8
	or rdx, rax
	add rcx, 1
	cmp rcx, r12
	jne 233b
	sub rdx, 1
	shr rdx, 63
	mov QWORD PTR [r15], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, QWORD PTR [r15+216]
	xor rdx, rdx
	sub rdx, QWORD PTR [r15]
	movq xmm6, rdx
	punpcklqdq xmm6, xmm6
	mov rcx, 0
	mov r8, r12
	shr r8, 4
	test r8, r8
	je 234f
236:
	movdqu xmm7, XMMWORD PTR [rbx+rcx*1]
	pand xmm7, xmm6
	movdqu XMMWORD PTR [rbx+rcx*1], xmm7
	add rcx, 16
	sub r8, 1
	jne 236b
	jmp 235f
234:
235:
	cmp rcx, r12
	je 237f
239:
	movzx eax, BYTE PTR [rbx+rcx*1]
	and rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 239b
	jmp 238f
237:
238:
	mov rax, QWORD PTR [r15]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+3632]
	ret
	.p2align 6

vg_aes_ocb_init:
	lea rsp, [rsp-2568]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov rbx, rdx
	mov rbp, rsi
	shr rbp, 2
	add rbp, 6
	mov r12, rcx
	add rcx, 512
	call {vg_aes_expand_key_scratch}
	xor rax, rax
	mov QWORD PTR [rbx+240], rax
	mov QWORD PTR [rbx+248], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 240
	mov rcx, 1
	mov r8, r12
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rbx, QWORD PTR [r12]
	mov rbp, QWORD PTR [r12+8]
	mov r12, QWORD PTR [r12+16]
	lea rsp, [rsp+2568]
	pxor xmm0, xmm0
	xor r11d, r11d
	lea rsp, [rsp-2576]
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
	lea rsp, [rsp+2576]
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

vg_aes_ocb_seal:
	lea rsp, [rsp-3632]
	mov rax, QWORD PTR [rsp+3640]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3648]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3656]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+3664]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	mov QWORD PTR [r15+2560], rax
	mov QWORD PTR [r15+2568], rdx
	mov r9, QWORD PTR [r15+216]
	mov rax, QWORD PTR [r15+248]
	or r9, rax
	shr r9, 5
	mov r10, r15
	add r10, 2560
	mov r11, 1
	movabs rsi, 157587932685088877
	test r9, r9
	je 20f
22:
	add r11, r11
	mov rax, r11
	mul rsi
	shr rax, 58
	ror rax, 60
	add rax, r15
	mov rdi, rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov rdx, QWORD PTR [r10+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	bswap rdx
	mov QWORD PTR [rdi+2568], rdx
	mov r10, rdi
	add r10, 2560
	shr r9, 1
	test r9, r9
	jne 22b
	jmp 21f
20:
21:
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
23:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 23b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	xor rax, rax
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rax
	xor rax, rax
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rax
	mov rbx, QWORD PTR [r15+240]
	mov rax, QWORD PTR [r15+248]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+112], rcx
	shr rax, 4
	mov QWORD PTR [r15+248], rax
	mov rbp, 1
	test rax, rax
	je 24f
26:
	mov r12, QWORD PTR [r15+248]
	cmp r12, 8
	jb 27f
	mov r12, 8
	jmp 28f
27:
28:
	mov r13, 0
	mov rsi, r15
	add rsi, 384
29:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [rcx+2560]
	xor rdx, QWORD PTR [rcx+2568]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [rbx]
	mov rdx, QWORD PTR [rbx+8]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rdx
	add rsi, 16
	add rbx, 16
	add rbp, 1
	add r13, 1
	cmp r13, r12
	jne 29b
	mov rdx, r15
	add rdx, 384
	mov rcx, r12
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov r13, 0
	mov rsi, r15
	add rsi, 384
210:
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [rsi]
	xor rdx, QWORD PTR [rsi+8]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	add rsi, 16
	add r13, 1
	cmp r13, r12
	jne 210b
	mov rax, QWORD PTR [r15+248]
	sub rax, r12
	mov QWORD PTR [r15+248], rax
	jne 26b
	jmp 25f
24:
25:
	mov r12, QWORD PTR [r15+112]
	test r12, r12
	je 211f
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	xor rax, rax
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rax
	mov rsi, r15
	add rsi, 384
	mov rcx, 0
213:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 213b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+384]
	mov rdx, QWORD PTR [r15+392]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rdx
	mov rdx, r15
	add rdx, 384
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [r15+384]
	xor rdx, QWORD PTR [r15+392]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	jmp 212f
211:
212:
	mov r13, QWORD PTR [r15+216]
	shr r13, 4
	test r13, r13
	je 214f
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 216f
218:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 218b
	jmp 217f
216:
217:
	test r12, r12
	je 219f
221:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 221b
	jmp 220f
219:
220:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	mov rdx, QWORD PTR [r15+208]
	mov rcx, r13
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+272]
	mov rdx, QWORD PTR [r15+280]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 222f
224:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 224b
	jmp 223f
222:
223:
	test r12, r12
	je 225f
227:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 227b
	jmp 226f
225:
226:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+208]
	mov rax, QWORD PTR [r15+216]
	mov r12, rax
	and r12, 15
	sub rax, r12
	add rbx, rax
	test r12, r12
	je 228f
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
230:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 230b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+128]
	xor rdx, QWORD PTR [r15+136]
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rdx
	mov rcx, 0
231:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 231b
	jmp 229f
228:
229:
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+16]
	xor rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+64]
	xor rdx, QWORD PTR [r15+72]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rdx
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	xor rax, QWORD PTR [r15+48]
	xor rdx, QWORD PTR [r15+56]
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rdx
	mov rbx, r15
	mov rsi, QWORD PTR [r15+304]
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
232:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 232b
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+3632]
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
	lea rsp, [rsp-3640]
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
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
	lea rsp, [rsp+3640]
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

vg_aes_ocb_open:
	lea rsp, [rsp-3632]
	mov rax, QWORD PTR [rsp+3640]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3648]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3656]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+3664]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	mov QWORD PTR [r15+2560], rax
	mov QWORD PTR [r15+2568], rdx
	mov r9, QWORD PTR [r15+216]
	mov rax, QWORD PTR [r15+248]
	or r9, rax
	shr r9, 5
	mov r10, r15
	add r10, 2560
	mov r11, 1
	movabs rsi, 157587932685088877
	test r9, r9
	je 20f
22:
	add r11, r11
	mov rax, r11
	mul rsi
	shr rax, 58
	ror rax, 60
	add rax, r15
	mov rdi, rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov rdx, QWORD PTR [r10+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	bswap rdx
	mov QWORD PTR [rdi+2568], rdx
	mov r10, rdi
	add r10, 2560
	shr r9, 1
	test r9, r9
	jne 22b
	jmp 21f
20:
21:
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
23:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 23b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	xor rax, rax
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rax
	xor rax, rax
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rax
	mov rbx, QWORD PTR [r15+240]
	mov rax, QWORD PTR [r15+248]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+112], rcx
	shr rax, 4
	mov QWORD PTR [r15+248], rax
	mov rbp, 1
	test rax, rax
	je 24f
26:
	mov r12, QWORD PTR [r15+248]
	cmp r12, 8
	jb 27f
	mov r12, 8
	jmp 28f
27:
28:
	mov r13, 0
	mov rsi, r15
	add rsi, 384
29:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [rcx+2560]
	xor rdx, QWORD PTR [rcx+2568]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [rbx]
	mov rdx, QWORD PTR [rbx+8]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rdx
	add rsi, 16
	add rbx, 16
	add rbp, 1
	add r13, 1
	cmp r13, r12
	jne 29b
	mov rdx, r15
	add rdx, 384
	mov rcx, r12
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov r13, 0
	mov rsi, r15
	add rsi, 384
210:
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [rsi]
	xor rdx, QWORD PTR [rsi+8]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	add rsi, 16
	add r13, 1
	cmp r13, r12
	jne 210b
	mov rax, QWORD PTR [r15+248]
	sub rax, r12
	mov QWORD PTR [r15+248], rax
	jne 26b
	jmp 25f
24:
25:
	mov r12, QWORD PTR [r15+112]
	test r12, r12
	je 211f
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	xor rax, rax
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rax
	mov rsi, r15
	add rsi, 384
	mov rcx, 0
213:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 213b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+384]
	mov rdx, QWORD PTR [r15+392]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rdx
	mov rdx, r15
	add rdx, 384
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [r15+384]
	xor rdx, QWORD PTR [r15+392]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	jmp 212f
211:
212:
	mov r13, QWORD PTR [r15+216]
	shr r13, 4
	test r13, r13
	je 214f
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 216f
218:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 218b
	jmp 217f
216:
217:
	test r12, r12
	je 219f
221:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 221b
	jmp 220f
219:
220:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	mov rdx, QWORD PTR [r15+208]
	mov rcx, r13
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_decrypt_blocks}
	mov rax, QWORD PTR [r15+272]
	mov rdx, QWORD PTR [r15+280]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 222f
224:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 224b
	jmp 223f
222:
223:
	test r12, r12
	je 225f
227:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 227b
	jmp 226f
225:
226:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+208]
	mov rax, QWORD PTR [r15+216]
	mov r12, rax
	and r12, 15
	sub rax, r12
	add rbx, rax
	test r12, r12
	je 228f
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rcx, 0
230:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 230b
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
231:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 231b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+128]
	xor rdx, QWORD PTR [r15+136]
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rdx
	jmp 229f
228:
229:
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+16]
	xor rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+64]
	xor rdx, QWORD PTR [r15+72]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rdx
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	xor rax, QWORD PTR [r15+48]
	xor rdx, QWORD PTR [r15+56]
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rdx
	mov rbx, QWORD PTR [r15+304]
	mov rsi, r15
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
232:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 232b
	xor rdx, rdx
	mov rcx, 0
	mov r12, QWORD PTR [r15+224]
233:
	movzx eax, BYTE PTR [r15+rcx*1]
	movzx r8d, BYTE PTR [r15+rcx*1+128]
	xor rax, r8
	or rdx, rax
	add rcx, 1
	cmp rcx, r12
	jne 233b
	sub rdx, 1
	shr rdx, 63
	mov QWORD PTR [r15], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, QWORD PTR [r15+216]
	xor rdx, rdx
	sub rdx, QWORD PTR [r15]
	movq xmm6, rdx
	punpcklqdq xmm6, xmm6
	mov rcx, 0
	mov r8, r12
	shr r8, 4
	test r8, r8
	je 234f
236:
	movdqu xmm7, XMMWORD PTR [rbx+rcx*1]
	pand xmm7, xmm6
	movdqu XMMWORD PTR [rbx+rcx*1], xmm7
	add rcx, 16
	sub r8, 1
	jne 236b
	jmp 235f
234:
235:
	cmp rcx, r12
	je 237f
239:
	movzx eax, BYTE PTR [rbx+rcx*1]
	and rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 239b
	jmp 238f
237:
238:
	mov rax, QWORD PTR [r15]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+3632]
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
	lea rsp, [rsp-3640]
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
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
	lea rsp, [rsp+3640]
	mov eax, eax
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
