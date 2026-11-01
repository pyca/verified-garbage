// The functions of `src/aes_gcm_siv.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_siv_seal_aesni:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
26:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 27f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
29:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 29b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 28f
27:
28:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 210f
	mov r14, rbx
	mov rcx, r14
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
	jmp 211f
210:
211:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 216f
218:
	mov r14d, 64
	cmp rbx, r14
	jb 219f
	jmp 220f
219:
	mov r14, rbx
220:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
221:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 221b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 223f
222:
223:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 225f
227:
	mov r14d, 64
	cmp rbx, r14
	jb 228f
	jmp 229f
228:
	mov r14, rbx
229:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
230:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 230b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 227b
	jmp 226f
225:
226:
	test rbp, rbp
	je 231f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 232f
231:
232:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 234f
236:
	mov r14d, 64
	cmp rbx, r14
	jb 237f
	jmp 238f
237:
	mov r14, rbx
238:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
239:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 239b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
240:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 240b
	sub rbx, r14
	jne 236b
	jmp 235f
234:
235:
	test rbp, rbp
	je 241f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	jmp 242f
241:
242:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_aesni:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
28:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 28b
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 29f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 212f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 214f
	mov r14, rbx
	mov rcx, r14
216:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 216b
	jmp 215f
214:
215:
	test rbp, rbp
	je 217f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 218f
217:
218:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
222:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 222b
	jmp 221f
220:
221:
	test rbp, rbp
	je 223f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 224f
223:
224:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 213f
212:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 226f
228:
	mov r14d, 64
	cmp rbx, r14
	jb 229f
	jmp 230f
229:
	mov r14, rbx
230:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
231:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 231b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 228b
	jmp 227f
226:
227:
	test rbp, rbp
	je 232f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 233f
232:
233:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 235f
237:
	mov r14d, 64
	cmp rbx, r14
	jb 238f
	jmp 239f
238:
	mov r14, rbx
239:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 237b
	jmp 236f
235:
236:
	test rbp, rbp
	je 241f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
213:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 244f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
246:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 246b
	jmp 245f
244:
245:
	cmp r10, rbp
	je 247f
249:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 249b
	jmp 248f
247:
248:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_seal_aesni_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
26:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 27f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
29:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 29b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 28f
27:
28:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 210f
	mov r14, rbx
	mov rcx, r14
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
	jmp 211f
210:
211:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 216f
218:
	mov r14d, 64
	cmp rbx, r14
	jb 219f
	jmp 220f
219:
	mov r14, rbx
220:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
221:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 221b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 223f
222:
223:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 225f
227:
	mov r14d, 64
	cmp rbx, r14
	jb 228f
	jmp 229f
228:
	mov r14, rbx
229:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
230:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 230b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 227b
	jmp 226f
225:
226:
	test rbp, rbp
	je 231f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 232f
231:
232:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 234f
236:
	mov r14d, 64
	cmp rbx, r14
	jb 237f
	jmp 238f
237:
	mov r14, rbx
238:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
239:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 239b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
240:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 240b
	sub rbx, r14
	jne 236b
	jmp 235f
234:
235:
	test rbp, rbp
	je 241f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	jmp 242f
241:
242:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_aesni_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
28:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 28b
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 29f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 212f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 214f
	mov r14, rbx
	mov rcx, r14
216:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 216b
	jmp 215f
214:
215:
	test rbp, rbp
	je 217f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 218f
217:
218:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
222:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 222b
	jmp 221f
220:
221:
	test rbp, rbp
	je 223f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 224f
223:
224:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 213f
212:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 226f
228:
	mov r14d, 64
	cmp rbx, r14
	jb 229f
	jmp 230f
229:
	mov r14, rbx
230:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
231:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 231b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 228b
	jmp 227f
226:
227:
	test rbp, rbp
	je 232f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 233f
232:
233:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 235f
237:
	mov r14d, 64
	cmp rbx, r14
	jb 238f
	jmp 239f
238:
	mov r14, rbx
239:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 237b
	jmp 236f
235:
236:
	test rbp, rbp
	je 241f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
213:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 244f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
246:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 246b
	jmp 245f
244:
245:
	cmp r10, rbp
	je 247f
249:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 249b
	jmp 248f
247:
248:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

// vg_aes_gcm_siv_seal_aesni_pclmul_avx: the function `vg_aes_gcm_siv_seal_aesni_pclmul`

// vg_aes_gcm_siv_open_aesni_pclmul_avx: the function `vg_aes_gcm_siv_open_aesni_pclmul`

vg_aes_gcm_siv_seal_aesni_vpclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 26f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
28:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 28b
	vzeroupper
	test rcx, rcx
	je 29f
211:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 211b
	jmp 210f
29:
210:
	jmp 27f
26:
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
27:
	jmp 25f
24:
25:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 216f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 218f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
220:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 220b
	vzeroupper
	test rcx, rcx
	je 221f
223:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 223b
	jmp 222f
221:
222:
	jmp 219f
218:
224:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 224b
219:
	jmp 217f
216:
217:
	test rbp, rbp
	je 225f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 228f
230:
	mov r14d, 64
	cmp rbx, r14
	jb 231f
	jmp 232f
231:
	mov r14, rbx
232:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 233f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
235:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 235b
	vzeroupper
	test rcx, rcx
	je 236f
238:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 238b
	jmp 237f
236:
237:
	jmp 234f
233:
239:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 239b
234:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 230b
	jmp 229f
228:
229:
	test rbp, rbp
	je 240f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
242:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 242b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 241f
240:
241:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 243f
245:
	mov r14d, 64
	cmp rbx, r14
	jb 246f
	jmp 247f
246:
	mov r14, rbx
247:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 248f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
250:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 250b
	vzeroupper
	test rcx, rcx
	je 251f
253:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 253b
	jmp 252f
251:
252:
	jmp 249f
248:
254:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 254b
249:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 245b
	jmp 244f
243:
244:
	test rbp, rbp
	je 255f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
257:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 257b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 256f
255:
256:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 258f
260:
	mov r14d, 64
	cmp rbx, r14
	jb 261f
	jmp 262f
261:
	mov r14, rbx
262:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
263:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 263b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 264f
266:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 270b
265:
	sub rbx, r14
	jne 260b
	jmp 259f
258:
259:
	test rbp, rbp
	je 271f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	jmp 272f
271:
272:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_aesni_vpclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 28f
210:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 210b
	vzeroupper
	test rcx, rcx
	je 211f
213:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 213b
	jmp 212f
211:
212:
	jmp 29f
28:
214:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 214b
29:
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 215f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 218f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 222f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
224:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 224b
	vzeroupper
	test rcx, rcx
	je 225f
227:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 227b
	jmp 226f
225:
226:
	jmp 223f
222:
228:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 228b
223:
	jmp 221f
220:
221:
	test rbp, rbp
	je 229f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 230f
229:
230:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 232f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 234f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
236:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 236b
	vzeroupper
	test rcx, rcx
	je 237f
239:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 239b
	jmp 238f
237:
238:
	jmp 235f
234:
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
235:
	jmp 233f
232:
233:
	test rbp, rbp
	je 241f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 219f
218:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 244f
246:
	mov r14d, 64
	cmp rbx, r14
	jb 247f
	jmp 248f
247:
	mov r14, rbx
248:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 249f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
251:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 251b
	vzeroupper
	test rcx, rcx
	je 252f
254:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 254b
	jmp 253f
252:
253:
	jmp 250f
249:
255:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 255b
250:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 246b
	jmp 245f
244:
245:
	test rbp, rbp
	je 256f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
258:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 258b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 257f
256:
257:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 259f
261:
	mov r14d, 64
	cmp rbx, r14
	jb 262f
	jmp 263f
262:
	mov r14, rbx
263:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 264f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
266:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
265:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 261b
	jmp 260f
259:
260:
	test rbp, rbp
	je 271f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 272f
271:
272:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
219:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 274f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
276:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 276b
	jmp 275f
274:
275:
	cmp r10, rbp
	je 277f
279:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 279b
	jmp 278f
277:
278:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_seal_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
26:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 27f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
29:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 29b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 28f
27:
28:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 210f
	mov r14, rbx
	mov rcx, r14
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
	jmp 211f
210:
211:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 216f
218:
	mov r14d, 64
	cmp rbx, r14
	jb 219f
	jmp 220f
219:
	mov r14, rbx
220:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
221:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 221b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 223f
222:
223:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 225f
227:
	mov r14d, 64
	cmp rbx, r14
	jb 228f
	jmp 229f
228:
	mov r14, rbx
229:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
230:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 230b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 227b
	jmp 226f
225:
226:
	test rbp, rbp
	je 231f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 232f
231:
232:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 234f
236:
	mov r14d, 64
	cmp rbx, r14
	jb 237f
	jmp 238f
237:
	mov r14, rbx
238:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
239:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 239b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
240:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 240b
	sub rbx, r14
	jne 236b
	jmp 235f
234:
235:
	test rbp, rbp
	je 241f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	jmp 242f
241:
242:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
28:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 28b
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 29f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 212f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 214f
	mov r14, rbx
	mov rcx, r14
216:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 216b
	jmp 215f
214:
215:
	test rbp, rbp
	je 217f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 218f
217:
218:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
222:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 222b
	jmp 221f
220:
221:
	test rbp, rbp
	je 223f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 224f
223:
224:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 213f
212:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 226f
228:
	mov r14d, 64
	cmp rbx, r14
	jb 229f
	jmp 230f
229:
	mov r14, rbx
230:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
231:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 231b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 228b
	jmp 227f
226:
227:
	test rbp, rbp
	je 232f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 233f
232:
233:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 235f
237:
	mov r14d, 64
	cmp rbx, r14
	jb 238f
	jmp 239f
238:
	mov r14, rbx
239:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 237b
	jmp 236f
235:
236:
	test rbp, rbp
	je 241f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
213:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 244f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
246:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 246b
	jmp 245f
244:
245:
	cmp r10, rbp
	je 247f
249:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 249b
	jmp 248f
247:
248:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_seal:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
26:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 27f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
29:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 29b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 28f
27:
28:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 210f
	mov r14, rbx
	mov rcx, r14
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
	jmp 211f
210:
211:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 216f
218:
	mov r14d, 64
	cmp rbx, r14
	jb 219f
	jmp 220f
219:
	mov r14, rbx
220:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
221:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 221b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 223f
222:
223:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 225f
227:
	mov r14d, 64
	cmp rbx, r14
	jb 228f
	jmp 229f
228:
	mov r14, rbx
229:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
230:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 230b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 227b
	jmp 226f
225:
226:
	test rbp, rbp
	je 231f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 232f
231:
232:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 234f
236:
	mov r14d, 64
	cmp rbx, r14
	jb 237f
	jmp 238f
237:
	mov r14, rbx
238:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
239:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 239b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
240:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 240b
	sub rbx, r14
	jne 236b
	jmp 235f
234:
235:
	test rbp, rbp
	je 241f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	jmp 242f
241:
242:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
28:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 28b
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 29f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 212f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 214f
	mov r14, rbx
	mov rcx, r14
216:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 216b
	jmp 215f
214:
215:
	test rbp, rbp
	je 217f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 218f
217:
218:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
222:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 222b
	jmp 221f
220:
221:
	test rbp, rbp
	je 223f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 224f
223:
224:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 213f
212:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 226f
228:
	mov r14d, 64
	cmp rbx, r14
	jb 229f
	jmp 230f
229:
	mov r14, rbx
230:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
231:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 231b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 228b
	jmp 227f
226:
227:
	test rbp, rbp
	je 232f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 233f
232:
233:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 235f
237:
	mov r14d, 64
	cmp rbx, r14
	jb 238f
	jmp 239f
238:
	mov r14, rbx
239:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 237b
	jmp 236f
235:
236:
	test rbp, rbp
	je 241f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
213:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 244f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
246:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 246b
	jmp 245f
244:
245:
	cmp r10, rbp
	je 247f
249:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 249b
	jmp 248f
247:
248:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_seal_vaes:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 26f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
28:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 28b
	vzeroupper
	test rcx, rcx
	je 29f
211:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 211b
	jmp 210f
29:
210:
	jmp 27f
26:
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
27:
	jmp 25f
24:
25:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 216f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 218f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
220:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 220b
	vzeroupper
	test rcx, rcx
	je 221f
223:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 223b
	jmp 222f
221:
222:
	jmp 219f
218:
224:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 224b
219:
	jmp 217f
216:
217:
	test rbp, rbp
	je 225f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 228f
230:
	mov r14d, 64
	cmp rbx, r14
	jb 231f
	jmp 232f
231:
	mov r14, rbx
232:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 233f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
235:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 235b
	vzeroupper
	test rcx, rcx
	je 236f
238:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 238b
	jmp 237f
236:
237:
	jmp 234f
233:
239:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 239b
234:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 230b
	jmp 229f
228:
229:
	test rbp, rbp
	je 240f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
242:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 242b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 241f
240:
241:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 243f
245:
	mov r14d, 64
	cmp rbx, r14
	jb 246f
	jmp 247f
246:
	mov r14, rbx
247:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 248f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
250:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 250b
	vzeroupper
	test rcx, rcx
	je 251f
253:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 253b
	jmp 252f
251:
252:
	jmp 249f
248:
254:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 254b
249:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 245b
	jmp 244f
243:
244:
	test rbp, rbp
	je 255f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
257:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 257b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 256f
255:
256:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 258f
260:
	mov r14d, 64
	cmp rbx, r14
	jb 261f
	jmp 262f
261:
	mov r14, rbx
262:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
263:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 263b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 264f
266:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 270b
265:
	sub rbx, r14
	jne 260b
	jmp 259f
258:
259:
	test rbp, rbp
	je 271f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	jmp 272f
271:
272:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_vaes:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 28f
210:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 210b
	vzeroupper
	test rcx, rcx
	je 211f
213:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 213b
	jmp 212f
211:
212:
	jmp 29f
28:
214:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 214b
29:
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 215f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 218f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 222f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
224:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 224b
	vzeroupper
	test rcx, rcx
	je 225f
227:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 227b
	jmp 226f
225:
226:
	jmp 223f
222:
228:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 228b
223:
	jmp 221f
220:
221:
	test rbp, rbp
	je 229f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 230f
229:
230:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 232f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 234f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
236:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 236b
	vzeroupper
	test rcx, rcx
	je 237f
239:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 239b
	jmp 238f
237:
238:
	jmp 235f
234:
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
235:
	jmp 233f
232:
233:
	test rbp, rbp
	je 241f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 219f
218:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 244f
246:
	mov r14d, 64
	cmp rbx, r14
	jb 247f
	jmp 248f
247:
	mov r14, rbx
248:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 249f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
251:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 251b
	vzeroupper
	test rcx, rcx
	je 252f
254:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 254b
	jmp 253f
252:
253:
	jmp 250f
249:
255:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 255b
250:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 246b
	jmp 245f
244:
245:
	test rbp, rbp
	je 256f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
258:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 258b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 257f
256:
257:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 259f
261:
	mov r14d, 64
	cmp rbx, r14
	jb 262f
	jmp 263f
262:
	mov r14, rbx
263:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 264f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
266:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
265:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 261b
	jmp 260f
259:
260:
	test rbp, rbp
	je 271f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 272f
271:
272:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
219:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 274f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
276:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 276b
	jmp 275f
274:
275:
	cmp r10, rbp
	je 277f
279:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 279b
	jmp 278f
277:
278:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_seal_vaes_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 26f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
28:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 28b
	vzeroupper
	test rcx, rcx
	je 29f
211:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 211b
	jmp 210f
29:
210:
	jmp 27f
26:
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
27:
	jmp 25f
24:
25:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 216f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 218f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
220:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 220b
	vzeroupper
	test rcx, rcx
	je 221f
223:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 223b
	jmp 222f
221:
222:
	jmp 219f
218:
224:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 224b
219:
	jmp 217f
216:
217:
	test rbp, rbp
	je 225f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 228f
230:
	mov r14d, 64
	cmp rbx, r14
	jb 231f
	jmp 232f
231:
	mov r14, rbx
232:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 233f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
235:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 235b
	vzeroupper
	test rcx, rcx
	je 236f
238:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 238b
	jmp 237f
236:
237:
	jmp 234f
233:
239:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 239b
234:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 230b
	jmp 229f
228:
229:
	test rbp, rbp
	je 240f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
242:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 242b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 241f
240:
241:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 243f
245:
	mov r14d, 64
	cmp rbx, r14
	jb 246f
	jmp 247f
246:
	mov r14, rbx
247:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 248f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
250:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 250b
	vzeroupper
	test rcx, rcx
	je 251f
253:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 253b
	jmp 252f
251:
252:
	jmp 249f
248:
254:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 254b
249:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 245b
	jmp 244f
243:
244:
	test rbp, rbp
	je 255f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
257:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 257b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 256f
255:
256:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 258f
260:
	mov r14d, 64
	cmp rbx, r14
	jb 261f
	jmp 262f
261:
	mov r14, rbx
262:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
263:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 263b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 264f
266:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 270b
265:
	sub rbx, r14
	jne 260b
	jmp 259f
258:
259:
	test rbp, rbp
	je 271f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	jmp 272f
271:
272:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_vaes_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 28f
210:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 210b
	vzeroupper
	test rcx, rcx
	je 211f
213:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 213b
	jmp 212f
211:
212:
	jmp 29f
28:
214:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 214b
29:
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 215f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 218f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 222f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
224:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 224b
	vzeroupper
	test rcx, rcx
	je 225f
227:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 227b
	jmp 226f
225:
226:
	jmp 223f
222:
228:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 228b
223:
	jmp 221f
220:
221:
	test rbp, rbp
	je 229f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 230f
229:
230:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 232f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 234f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
236:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 236b
	vzeroupper
	test rcx, rcx
	je 237f
239:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 239b
	jmp 238f
237:
238:
	jmp 235f
234:
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
235:
	jmp 233f
232:
233:
	test rbp, rbp
	je 241f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 219f
218:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 244f
246:
	mov r14d, 64
	cmp rbx, r14
	jb 247f
	jmp 248f
247:
	mov r14, rbx
248:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 249f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
251:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 251b
	vzeroupper
	test rcx, rcx
	je 252f
254:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 254b
	jmp 253f
252:
253:
	jmp 250f
249:
255:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 255b
250:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 246b
	jmp 245f
244:
245:
	test rbp, rbp
	je 256f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
258:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 258b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 257f
256:
257:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 259f
261:
	mov r14d, 64
	cmp rbx, r14
	jb 262f
	jmp 263f
262:
	mov r14, rbx
263:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 264f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
266:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
265:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 261b
	jmp 260f
259:
260:
	test rbp, rbp
	je 271f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 272f
271:
272:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
219:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 274f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
276:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 276b
	jmp 275f
274:
275:
	cmp r10, rbp
	je 277f
279:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 279b
	jmp 278f
277:
278:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_seal_vaes_vpclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 22f
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 24f
26:
	mov r14d, 64
	cmp rbx, r14
	jb 27f
	jmp 28f
27:
	mov r14, rbx
28:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 29f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
211:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 211b
	vzeroupper
	test rcx, rcx
	je 212f
214:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 214b
	jmp 213f
212:
213:
	jmp 210f
29:
215:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 215b
210:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 217f
216:
217:
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1512
	mov rdx, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r8]
	pshufb xmm7, xmm0
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm13, XMMWORD PTR [rax+32]
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm12, xmm10
	pxor xmm12, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm13, xmm10
	pxor xmm13, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm14, xmm10
	pxor xmm14, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm15, xmm10
	pxor xmm15, xmm8
	vinserti128 ymm15, ymm15, xmm14, 1
	vinserti128 ymm14, ymm13, xmm12, 1
	vinserti128 ymm13, ymm6, xmm5, 1
	vinserti128 ymm12, ymm4, xmm3, 1
	vinserti128 ymm0, ymm0, xmm0, 1
	vinserti128 ymm1, ymm1, xmm1, 1
	vmovdqa xmm2, xmm2
	vinserti128 ymm7, ymm15, xmm15, 1
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm15, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm3, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm14, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm4, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm13, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm5, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm12, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm6, ymm10, ymm8
	vmovdqu YMMWORD PTR [r11], ymm3
	vmovdqu YMMWORD PTR [r11+32], ymm4
	vmovdqu YMMWORD PTR [r11+64], ymm5
	vmovdqu YMMWORD PTR [r11+96], ymm6
	vmovdqu YMMWORD PTR [r11+128], ymm15
	vmovdqu YMMWORD PTR [r11+160], ymm14
	vmovdqu YMMWORD PTR [r11+192], ymm13
	vmovdqu YMMWORD PTR [r11+224], ymm12
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
219:
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vmovdqu ymm12, YMMWORD PTR [r11+32]
	vmovdqu ymm7, YMMWORD PTR [rdx+32]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+64]
	vmovdqu ymm7, YMMWORD PTR [rdx+64]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+96]
	vmovdqu ymm7, YMMWORD PTR [rdx+96]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+128]
	vmovdqu ymm7, YMMWORD PTR [rdx+128]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+160]
	vmovdqu ymm7, YMMWORD PTR [rdx+160]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+192]
	vmovdqu ymm7, YMMWORD PTR [rdx+192]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+224]
	vmovdqu ymm7, YMMWORD PTR [rdx+224]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11]
	vmovdqu ymm7, YMMWORD PTR [rdx]
	vpxor ymm7, ymm7, ymm2
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm7, ymm10, ymm8
	vextracti128 xmm11, ymm7, 1
	vpxor xmm2, xmm7, xmm11
	add rdx, 256
	sub r9, 16
	jne 219b
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 220f
222:
	mov r14d, 64
	cmp rbx, r14
	jb 223f
	jmp 224f
223:
	mov r14, rbx
224:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 225f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
227:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 227b
	vzeroupper
	test rcx, rcx
	je 228f
230:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 230b
	jmp 229f
228:
229:
	jmp 226f
225:
231:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 231b
226:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 222b
	jmp 221f
220:
221:
	test rbp, rbp
	je 232f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 233f
232:
233:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 235f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 237f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 239f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
241:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 241b
	vzeroupper
	test rcx, rcx
	je 242f
244:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 244b
	jmp 243f
242:
243:
	jmp 240f
239:
245:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 245b
240:
	jmp 238f
237:
238:
	test rbp, rbp
	je 246f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 247f
246:
247:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 249f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 251f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
253:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 253b
	vzeroupper
	test rcx, rcx
	je 254f
256:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 256b
	jmp 255f
254:
255:
	jmp 252f
251:
257:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 257b
252:
	jmp 250f
249:
250:
	test rbp, rbp
	je 258f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
260:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 260b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 259f
258:
259:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 236f
235:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 261f
263:
	mov r14d, 64
	cmp rbx, r14
	jb 264f
	jmp 265f
264:
	mov r14, rbx
265:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 266f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
268:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 268b
	vzeroupper
	test rcx, rcx
	je 269f
271:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 271b
	jmp 270f
269:
270:
	jmp 267f
266:
272:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 272b
267:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 263b
	jmp 262f
261:
262:
	test rbp, rbp
	je 273f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
275:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 275b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 274f
273:
274:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 276f
278:
	mov r14d, 64
	cmp rbx, r14
	jb 279f
	jmp 280f
279:
	mov r14, rbx
280:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 281f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
283:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 283b
	vzeroupper
	test rcx, rcx
	je 284f
286:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 286b
	jmp 285f
284:
285:
	jmp 282f
281:
287:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 287b
282:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 278b
	jmp 277f
276:
277:
	test rbp, rbp
	je 288f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
290:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 290b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 289f
288:
289:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
236:
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 291f
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1768
	mov r12, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	vinserti128 ymm0, ymm0, xmm0, 1
	movabs r10, 1
	vmovq xmm15, r10
	vmovdqu xmm14, XMMWORD PTR [rdx]
	vpaddd xmm13, xmm14, xmm15
	vinserti128 ymm14, ymm14, xmm13, 1
	movabs r10, 2
	vmovq xmm15, r10
	vinserti128 ymm15, ymm15, xmm15, 1
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r12
293:
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 294f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 296f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 297f
296:
297:
	jmp 295f
294:
295:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+32]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+32], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+64]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+64], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+96]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+96], ymm6
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 298f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 2100f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 2101f
2100:
2101:
	jmp 299f
298:
299:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx+128]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+160]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+160], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+192]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+192], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+224]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+224], ymm6
	add rdx, 256
	sub r9, 16
	jne 293b
	vmovdqu XMMWORD PTR [rax], xmm14
	vzeroupper
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2102f
2104:
	mov r14d, 64
	cmp rbx, r14
	jb 2105f
	jmp 2106f
2105:
	mov r14, rbx
2106:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2107:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2107b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2108f
2110:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2110b
	vzeroupper
	test rcx, rcx
	je 2111f
2113:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2113b
	jmp 2112f
2111:
2112:
	jmp 2109f
2108:
2114:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2114b
2109:
	sub rbx, r14
	jne 2104b
	jmp 2103f
2102:
2103:
	test rbp, rbp
	je 2115f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2117:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2117b
	jmp 2116f
2115:
2116:
	jmp 292f
291:
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2118f
2120:
	mov r14d, 64
	cmp rbx, r14
	jb 2121f
	jmp 2122f
2121:
	mov r14, rbx
2122:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2123:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2123b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2124f
2126:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2126b
	vzeroupper
	test rcx, rcx
	je 2127f
2129:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2129b
	jmp 2128f
2127:
2128:
	jmp 2125f
2124:
2130:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2130b
2125:
	sub rbx, r14
	jne 2120b
	jmp 2119f
2118:
2119:
	test rbp, rbp
	je 2131f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2133:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2133b
	jmp 2132f
2131:
2132:
292:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_vaes_vpclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 22f
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 24f
26:
	mov r14d, 64
	cmp rbx, r14
	jb 27f
	jmp 28f
27:
	mov r14, rbx
28:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 29f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
211:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 211b
	vzeroupper
	test rcx, rcx
	je 212f
214:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 214b
	jmp 213f
212:
213:
	jmp 210f
29:
215:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 215b
210:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 217f
216:
217:
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1768
	mov r12, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r8]
	pshufb xmm7, xmm0
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm13, XMMWORD PTR [rax+32]
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm12, xmm10
	pxor xmm12, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm13, xmm10
	pxor xmm13, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm14, xmm10
	pxor xmm14, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm15, xmm10
	pxor xmm15, xmm8
	vinserti128 ymm15, ymm15, xmm14, 1
	vinserti128 ymm14, ymm13, xmm12, 1
	vinserti128 ymm13, ymm6, xmm5, 1
	vinserti128 ymm12, ymm4, xmm3, 1
	vinserti128 ymm0, ymm0, xmm0, 1
	vinserti128 ymm1, ymm1, xmm1, 1
	vmovdqa xmm2, xmm2
	vinserti128 ymm7, ymm15, xmm15, 1
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm15, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm3, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm14, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm4, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm13, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm5, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm12, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm6, ymm10, ymm8
	vmovdqu YMMWORD PTR [r11], ymm3
	vmovdqu YMMWORD PTR [r11+32], ymm4
	vmovdqu YMMWORD PTR [r11+64], ymm5
	vmovdqu YMMWORD PTR [r11+96], ymm6
	vmovdqu YMMWORD PTR [r11+128], ymm15
	vmovdqu YMMWORD PTR [r11+160], ymm14
	vmovdqu YMMWORD PTR [r11+192], ymm13
	vmovdqu YMMWORD PTR [r11+224], ymm12
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
	movabs r10, 1
	vmovq xmm15, r10
	vmovdqu xmm14, XMMWORD PTR [rdx]
	vpaddd xmm13, xmm14, xmm15
	vinserti128 ymm14, ymm14, xmm13, 1
	movabs r10, 2
	vmovq xmm15, r10
	vinserti128 ymm15, ymm15, xmm15, 1
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r12
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 219f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 221f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 222f
221:
222:
	jmp 220f
219:
220:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+32]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+32], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+64]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+64], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+96]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+96], ymm6
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 223f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 225f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 226f
225:
226:
	jmp 224f
223:
224:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx+128]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+160]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+160], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+192]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+192], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+224]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+224], ymm6
	cmp r9, 32
	jb 227f
229:
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+32]
	vmovdqu ymm7, YMMWORD PTR [rdx+32]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+64]
	vmovdqu ymm7, YMMWORD PTR [rdx+64]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+96]
	vmovdqu ymm7, YMMWORD PTR [rdx+96]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+128]
	vmovdqu ymm7, YMMWORD PTR [rdx+128]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 230f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 232f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 233f
232:
233:
	jmp 231f
230:
231:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx+256]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx+256], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+288]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+288], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+320]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+320], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+352]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+352], ymm6
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+160]
	vmovdqu ymm7, YMMWORD PTR [rdx+160]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+192]
	vmovdqu ymm7, YMMWORD PTR [rdx+192]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+224]
	vmovdqu ymm7, YMMWORD PTR [rdx+224]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11]
	vmovdqu ymm7, YMMWORD PTR [rdx]
	vpxor ymm7, ymm7, ymm2
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm7, ymm10, ymm8
	vextracti128 xmm11, ymm7, 1
	vpxor xmm2, xmm7, xmm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 234f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 236f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 237f
236:
237:
	jmp 235f
234:
235:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx+384]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx+384], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+416]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+416], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+448]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+448], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+480]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+480], ymm6
	add rdx, 256
	sub r9, 16
	cmp r9, 32
	jae 229b
	jmp 228f
227:
228:
	vmovdqu XMMWORD PTR [rax], xmm14
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vmovdqu ymm12, YMMWORD PTR [r11+32]
	vmovdqu ymm7, YMMWORD PTR [rdx+32]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+64]
	vmovdqu ymm7, YMMWORD PTR [rdx+64]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+96]
	vmovdqu ymm7, YMMWORD PTR [rdx+96]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+128]
	vmovdqu ymm7, YMMWORD PTR [rdx+128]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+160]
	vmovdqu ymm7, YMMWORD PTR [rdx+160]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+192]
	vmovdqu ymm7, YMMWORD PTR [rdx+192]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+224]
	vmovdqu ymm7, YMMWORD PTR [rdx+224]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11]
	vmovdqu ymm7, YMMWORD PTR [rdx]
	vpxor ymm7, ymm7, ymm2
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm7, ymm10, ymm8
	vextracti128 xmm11, ymm7, 1
	vpxor xmm2, xmm7, xmm11
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 238f
240:
	mov r14d, 64
	cmp rbx, r14
	jb 241f
	jmp 242f
241:
	mov r14, rbx
242:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
243:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 243b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 244f
246:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 246b
	vzeroupper
	test rcx, rcx
	je 247f
249:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 249b
	jmp 248f
247:
248:
	jmp 245f
244:
250:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 250b
245:
	sub rbx, r14
	jne 240b
	jmp 239f
238:
239:
	test rbp, rbp
	je 251f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
253:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 253b
	jmp 252f
251:
252:
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 254f
256:
	mov r14d, 64
	cmp rbx, r14
	jb 257f
	jmp 258f
257:
	mov r14, rbx
258:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 259f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
261:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 261b
	vzeroupper
	test rcx, rcx
	je 262f
264:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 264b
	jmp 263f
262:
263:
	jmp 260f
259:
265:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 265b
260:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 256b
	jmp 255f
254:
255:
	test rbp, rbp
	je 266f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
268:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 268b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 267f
266:
267:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 269f
271:
	mov r14d, 64
	cmp rbx, r14
	jb 272f
	jmp 273f
272:
	mov r14, rbx
273:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
274:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 274b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 275f
277:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 277b
	vzeroupper
	test rcx, rcx
	je 278f
280:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 280b
	jmp 279f
278:
279:
	jmp 276f
275:
281:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 281b
276:
	sub rbx, r14
	jne 271b
	jmp 270f
269:
270:
	test rbp, rbp
	je 282f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
284:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 284b
	jmp 283f
282:
283:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 285f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 287f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 289f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
291:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 291b
	vzeroupper
	test rcx, rcx
	je 292f
294:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 294b
	jmp 293f
292:
293:
	jmp 290f
289:
295:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 295b
290:
	jmp 288f
287:
288:
	test rbp, rbp
	je 296f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
298:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 298b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 297f
296:
297:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 299f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 2101f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2103:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2103b
	vzeroupper
	test rcx, rcx
	je 2104f
2106:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2106b
	jmp 2105f
2104:
2105:
	jmp 2102f
2101:
2107:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2107b
2102:
	jmp 2100f
299:
2100:
	test rbp, rbp
	je 2108f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2110:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2110b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 2109f
2108:
2109:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 286f
285:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2111f
2113:
	mov r14d, 64
	cmp rbx, r14
	jb 2114f
	jmp 2115f
2114:
	mov r14, rbx
2115:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2116f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2118:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2118b
	vzeroupper
	test rcx, rcx
	je 2119f
2121:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2121b
	jmp 2120f
2119:
2120:
	jmp 2117f
2116:
2122:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2122b
2117:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2113b
	jmp 2112f
2111:
2112:
	test rbp, rbp
	je 2123f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2125:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2125b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 2124f
2123:
2124:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2126f
2128:
	mov r14d, 64
	cmp rbx, r14
	jb 2129f
	jmp 2130f
2129:
	mov r14, rbx
2130:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2131f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2133:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2133b
	vzeroupper
	test rcx, rcx
	je 2134f
2136:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2136b
	jmp 2135f
2134:
2135:
	jmp 2132f
2131:
2137:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2137b
2132:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2128b
	jmp 2127f
2126:
2127:
	test rbp, rbp
	je 2138f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2140:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2140b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 2139f
2138:
2139:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
286:
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 2141f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
2143:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 2143b
	jmp 2142f
2141:
2142:
	cmp r10, rbp
	je 2144f
2146:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 2146b
	jmp 2145f
2144:
2145:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

// vg_aes_gcm_siv_seal_vaes_vpclmul_avx512: the function `vg_aes_gcm_siv_seal_vaes_vpclmul`

// vg_aes_gcm_siv_open_vaes_vpclmul_avx512: the function `vg_aes_gcm_siv_open_vaes_vpclmul`

vg_aes_gcm_siv_seal_vpclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 26f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
28:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 28b
	vzeroupper
	test rcx, rcx
	je 29f
211:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 211b
	jmp 210f
29:
210:
	jmp 27f
26:
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
27:
	jmp 25f
24:
25:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 216f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 218f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
220:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 220b
	vzeroupper
	test rcx, rcx
	je 221f
223:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 223b
	jmp 222f
221:
222:
	jmp 219f
218:
224:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 224b
219:
	jmp 217f
216:
217:
	test rbp, rbp
	je 225f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 228f
230:
	mov r14d, 64
	cmp rbx, r14
	jb 231f
	jmp 232f
231:
	mov r14, rbx
232:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 233f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
235:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 235b
	vzeroupper
	test rcx, rcx
	je 236f
238:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 238b
	jmp 237f
236:
237:
	jmp 234f
233:
239:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 239b
234:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 230b
	jmp 229f
228:
229:
	test rbp, rbp
	je 240f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
242:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 242b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 241f
240:
241:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 243f
245:
	mov r14d, 64
	cmp rbx, r14
	jb 246f
	jmp 247f
246:
	mov r14, rbx
247:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 248f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
250:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 250b
	vzeroupper
	test rcx, rcx
	je 251f
253:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 253b
	jmp 252f
251:
252:
	jmp 249f
248:
254:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 254b
249:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 245b
	jmp 244f
243:
244:
	test rbp, rbp
	je 255f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
257:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 257b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 256f
255:
256:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
23:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 258f
260:
	mov r14d, 64
	cmp rbx, r14
	jb 261f
	jmp 262f
261:
	mov r14, rbx
262:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
263:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 263b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 264f
266:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 270b
265:
	sub rbx, r14
	jne 260b
	jmp 259f
258:
259:
	test rbp, rbp
	je 271f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	jmp 272f
271:
272:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_vpclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	mov edx, DWORD PTR [rax+4]
	mov r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi], ebx
	mov DWORD PTR [rdi+4], ecx
	mov DWORD PTR [rdi+8], edx
	mov DWORD PTR [rdi+12], r8d
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 16
	add rdi, 8
	sub rcx, 1
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 28f
210:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 210b
	vzeroupper
	test rcx, rcx
	je 211f
213:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 213b
	jmp 212f
211:
212:
	jmp 29f
28:
214:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 214b
29:
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 215f
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 218f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 222f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
224:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 224b
	vzeroupper
	test rcx, rcx
	je 225f
227:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 227b
	jmp 226f
225:
226:
	jmp 223f
222:
228:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 228b
223:
	jmp 221f
220:
221:
	test rbp, rbp
	je 229f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 230f
229:
230:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 232f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 234f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
236:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 236b
	vzeroupper
	test rcx, rcx
	je 237f
239:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 239b
	jmp 238f
237:
238:
	jmp 235f
234:
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
235:
	jmp 233f
232:
233:
	test rbp, rbp
	je 241f
	mov rbx, rdi
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rdx
	mov QWORD PTR [rbx+8], rax
	mov rdi, rbx
	add rdi, 16
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
	jmp 219f
218:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 244f
246:
	mov r14d, 64
	cmp rbx, r14
	jb 247f
	jmp 248f
247:
	mov r14, rbx
248:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 249f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
251:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 251b
	vzeroupper
	test rcx, rcx
	je 252f
254:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 254b
	jmp 253f
252:
253:
	jmp 250f
249:
255:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 255b
250:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 246b
	jmp 245f
244:
245:
	test rbp, rbp
	je 256f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
258:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 258b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 257f
256:
257:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 259f
261:
	mov r14d, 64
	cmp rbx, r14
	jb 262f
	jmp 263f
262:
	mov r14, rbx
263:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 264f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
266:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rax
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
265:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 261b
	jmp 260f
259:
260:
	test rbp, rbp
	je 271f
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+488], rdx
	mov QWORD PTR [r15+496], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 272f
271:
272:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+128], rax
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rdx
219:
	mov rax, QWORD PTR [r15+96]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+104]
	mov QWORD PTR [r15+120], rax
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 274f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
276:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 276b
	jmp 275f
274:
275:
	cmp r10, rbp
	je 277f
279:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 279b
	jmp 278f
277:
278:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6
