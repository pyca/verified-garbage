// The functions of `src/dsa.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_parameter_search_init:
	cmp rsi, 128
	je 20f
	cmp rsi, 256
	je 22f
	cmp rsi, 384
	je 24f
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	jmp 25f
24:
	mov eax, 4096
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rsi
	mov rax, rsi
	shl rax, 15
	add rax, rsi
	mov QWORD PTR [rdi+16], rax
	mov rax, rsi
	shl rax, 9
	mov QWORD PTR [rdi+24], rax
	mov eax, 1
25:
	jmp 23f
22:
	mov eax, 4096
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rsi
	mov rax, rsi
	shl rax, 15
	add rax, rsi
	mov QWORD PTR [rdi+16], rax
	mov rax, rsi
	shl rax, 9
	mov QWORD PTR [rdi+24], rax
	mov eax, 1
23:
	jmp 21f
20:
	mov eax, 4096
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rsi
	mov rax, rsi
	shl rax, 15
	add rax, rsi
	mov QWORD PTR [rdi+16], rax
	mov rax, rsi
	shl rax, 9
	mov QWORD PTR [rdi+24], rax
	mov eax, 1
21:
	mov eax, eax
	xor esi, esi
	ret
	.p2align 6

vg_dsa_sign_random_prevalidated_adx:
	lea rsp, [rsp-248]
	mov QWORD PTR [rsp+40], rdi
	mov QWORD PTR [rsp+48], rsi
	mov QWORD PTR [rsp+56], rdx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], r8
	mov QWORD PTR [rsp+80], r9
	add rcx, r9
	mov QWORD PTR [rsp+168], rcx
	mov rax, 0
	mov QWORD PTR [rsp+144], rax
	mov rax, 8
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+120], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+128], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+136], rax
	mov rax, 0
	mov QWORD PTR [rsp+200], rax
	mov QWORD PTR [rsp+208], rax
	mov QWORD PTR [rsp+216], rax
	mov QWORD PTR [rsp+224], rax
	mov r10, QWORD PTR [rsp+168]
	mov r11, QWORD PTR [rsp+88]
	mov rsi, r10
	mov rcx, r11
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	sub r11, r8
	add r10, r11
	mov r11, r8
	mov rax, r9
	mov QWORD PTR [rsp+168], r10
	mov QWORD PTR [rsp+176], r11
	mov r9, rax
	mov r8, 255
	mov rcx, 127
	cmp rax, 128
	cmovb r8, rcx
	mov rcx, 63
	cmp rax, 64
	cmovb r8, rcx
	mov rcx, 31
	cmp rax, 32
	cmovb r8, rcx
	mov rcx, 15
	cmp rax, 16
	cmovb r8, rcx
	mov rcx, 7
	cmp rax, 8
	cmovb r8, rcx
	mov rcx, 3
	cmp rax, 4
	cmovb r8, rcx
	mov rcx, 1
	cmp rax, 2
	cmovb r8, rcx
	mov QWORD PTR [rsp+184], r8
	mov rax, 0
	mov rcx, 1
	cmp r11, 2
	cmovae rax, rcx
	cmp r9, 2
	cmovae rax, rcx
	cmp rax, 0
	je 25f
27:
	mov rax, 128
	mov QWORD PTR [rsp+160], rax
	mov rax, 4
	mov QWORD PTR [rsp+192], rax
28:
	mov rax, QWORD PTR [rsp+120]
	sub rax, QWORD PTR [rsp+144]
	cmp rax, QWORD PTR [rsp+176]
	jb 29f
	mov r10, QWORD PTR [rsp+112]
	add r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+176]
	mov rdx, rsp
	add rdx, 200
	add rdx, QWORD PTR [rsp+88]
	sub rdx, r11
	movzx eax, BYTE PTR [r10]
	and rax, QWORD PTR [rsp+184]
	mov BYTE PTR [rdx], al
	add r10, 1
	add rdx, 1
	sub r11, 1
	jne 211f
	jmp 212f
211:
213:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [rdx], al
	add r10, 1
	add rdx, 1
	sub r11, 1
	jne 213b
212:
	mov rax, QWORD PTR [rsp+144]
	add rax, QWORD PTR [rsp+176]
	mov QWORD PTR [rsp+144], rax
	mov rdx, rsp
	add rdx, 200
	add rdx, QWORD PTR [rsp+88]
	mov r10, QWORD PTR [rsp+168]
	mov r11, QWORD PTR [rsp+176]
	add r10, r11
	mov r8, 0
	mov r9, 0
214:
	sub rdx, 1
	sub r10, 1
	movzx eax, BYTE PTR [rdx]
	or r9, rax
	movzx ecx, BYTE PTR [r10]
	add rcx, r8
	sub rax, rcx
	shr rax, 63
	mov r8, rax
	sub r11, 1
	jne 214b
	mov rax, 0
	test r9, r9
	cmove r8, rax
	test r8, r8
	jne 215f
	mov rax, QWORD PTR [rsp+160]
	sub rax, 1
	mov QWORD PTR [rsp+160], rax
	je 217f
	jmp 218f
217:
	mov QWORD PTR [rsp+192], rax
218:
	jmp 216f
215:
	mov rax, 1
	mov QWORD PTR [rsp+192], rax
216:
	jmp 210f
29:
	mov rax, 2
	mov QWORD PTR [rsp+192], rax
210:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 4
	je 28b
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 1
	je 219f
	jmp 220f
219:
	mov rdi, QWORD PTR [rsp+40]
	mov rsi, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp+72]
	mov r8, QWORD PTR [rsp+80]
	mov r9, rsp
	add r9, 200
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+32], rax
	call {vg_dsa_sign_prevalidated_adx}
	mov eax, eax
	mov QWORD PTR [rsp+192], rax
	cmp rax, 0
	je 221f
	jmp 222f
221:
	mov rax, QWORD PTR [rsp+152]
	sub rax, 1
	mov QWORD PTR [rsp+152], rax
	jne 223f
	jmp 224f
223:
	mov rax, 4
	mov QWORD PTR [rsp+192], rax
224:
222:
220:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 4
	je 27b
	jmp 26f
25:
	mov QWORD PTR [rsp+192], rax
26:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 1
	jne 225f
	jmp 226f
225:
	mov r10, QWORD PTR [rsp+40]
	mov r11, QWORD PTR [rsp+48]
	mov rax, 0
227:
	mov BYTE PTR [r10], al
	add r10, 1
	sub r11, 1
	jne 227b
226:
	mov rax, 0
	mov QWORD PTR [rsp+200], rax
	mov QWORD PTR [rsp+208], rax
	mov QWORD PTR [rsp+216], rax
	mov QWORD PTR [rsp+224], rax
	mov rdx, QWORD PTR [rsp+56]
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+248]
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
	lea rsp, [rsp-264]
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
	lea rsp, [rsp+264]
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

vg_dsa_validate_private_key_adx:
	mov r11, r8
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov eax, 0
	mov QWORD PTR [r11+296], rax
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+304], rax
	mov QWORD PTR [r11+312], rax
	mov QWORD PTR [r11+344], rax
	mov QWORD PTR [r11+256], rdi
	mov QWORD PTR [r11+328], rdx
	mov QWORD PTR [r11+336], rcx
	mov rax, QWORD PTR [r11+256]
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+264], rax
	add rax, QWORD PTR [r11+336]
	mov QWORD PTR [r11+272], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+280], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+288], rax
	mov rdi, r11
	mov rax, QWORD PTR [r11+288]
	mov QWORD PTR [r11+304], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov QWORD PTR [rdi+176], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
	mov r9d, 0
25:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 26f
	jmp 27f
26:
	test rax, rax
	jne 28f
	jmp 29f
28:
	mov r8, rcx
	mov r9, rax
29:
27:
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov QWORD PTR [rdi+352], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rdx, QWORD PTR [rdi+176]
	cmp rdx, 128
	je 210f
	cmp rdx, 256
	je 212f
	cmp rdx, 384
	je 214f
	mov eax, 0
	jmp 215f
214:
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
215:
	jmp 213f
212:
	mov rax, r8
	xor rax, 28
	cmp rax, 1
	sbb rax, rax
	mov r10, rax
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
	or rax, r10
	mov r10, rax
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
	or rax, r10
213:
	jmp 211f
210:
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
211:
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	movzx eax, BYTE PTR [rsi+rcx*1-1]
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	movzx edx, BYTE PTR [rsi+rcx*1-1]
	and rax, rdx
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+344]
	mov rdx, QWORD PTR [rdi+352]
	cmp rdx, rax
	cmovb rax, rdx
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+360]
	test rax, rax
	je 216f
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 13312
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
223:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 224f
	jmp 225f
224:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
225:
	test rdx, rdx
	jne 223b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
229:
	test rdx, rdx
	jne 227b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
230:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 230b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
231:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 231b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
233:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 234f
	jmp 235f
234:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
235:
	test rdx, rdx
	jne 233b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
236:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 236b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
237:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 237b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 1
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
238:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 238b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
239:
	mov rbp, rdx
	and rbp, 7
	je 240f
	jmp 241f
240:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
241:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 239b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
242:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 243f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 245f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 247f
249:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 249b
	jmp 248f
247:
248:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
250:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
251:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
252:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 252b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
253:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 253b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
254:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 251b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
255:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 255b
	jmp 246f
245:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
256:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 256b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
257:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 257b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
258:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
259:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
260:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
261:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 258b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
262:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 262b
246:
	jmp 244f
243:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
263:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
264:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
265:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 265b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
266:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 266b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
267:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 264b
244:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
268:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
269:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 269b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
270:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 270b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
271:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 268b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
272:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
273:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 274f
276:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
277:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 277b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
278:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 278b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
279:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 276b
	jmp 275f
274:
275:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
280:
	mov rbp, rdx
	and rbp, 7
	je 281f
	jmp 282f
281:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
282:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 280b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14816
	mov rsi, rax
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
283:
	movzx eax, BYTE PTR [rsi]
	or r8, rax
	add rsi, 1
	sub rcx, 1
	jne 283b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 2
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
284:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 284b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
285:
	mov rbp, rdx
	and rbp, 7
	je 286f
	jmp 287f
286:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
287:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 285b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
288:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 288b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 289f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 291f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 293f
295:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 295b
	jmp 294f
293:
294:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
297:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
298:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 298b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
299:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 299b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2100:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 297b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2101:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2101b
	jmp 292f
291:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2102:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2103:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2103b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2104:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2105:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2105b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2106:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2107:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2104b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2108:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2108b
292:
	jmp 290f
289:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2109:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2110:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2111:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2112:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2113:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2110b
290:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2114:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2115:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2116f
	jmp 2117f
2116:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2117:
	test rdx, rdx
	jne 2115b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2118:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2118b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2119:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2120:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2121:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2122:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2123:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2122b
2124:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2125:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2126:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2126b
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	je 2127f
	mov r12, QWORD PTR [rdi+48]
	mov rax, r12
	add rax, 2
	mov rdx, QWORD PTR [rdi+216]
	imul rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+200]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2129:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	jmp 2128f
2127:
2128:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2125b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2124b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2130:
	mov rbp, rdx
	and rbp, 7
	je 2131f
	jmp 2132f
2131:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2132:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2130b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2133:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2134:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2135f
	jmp 2136f
2135:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2136:
	test rdx, rdx
	jne 2134b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r15, QWORD PTR [rbx]
	xor r15, 1
	mov r14, 1
2137:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2137b
	cmp r15, 1
	sbb rax, rax
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2138:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2139:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2140f
	jmp 2141f
2140:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2141:
	test rdx, rdx
	jne 2139b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
2142:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2142b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
2143:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2143b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2144:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2145:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2146f
	jmp 2147f
2146:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2147:
	test rdx, rdx
	jne 2145b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
2148:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
2149:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2149b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2150:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2151f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2153f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2155f
2157:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2157b
	jmp 2156f
2155:
2156:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2158:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2158b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2159:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2160:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2160b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2161:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2162:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2159b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2163:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2163b
	jmp 2154f
2153:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2164:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2165:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2165b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2166:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2167:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2167b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2168:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2169:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2166b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2170:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2170b
2154:
	jmp 2152f
2151:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2171:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2172:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2173:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2174:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2174b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2175:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2175b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2172b
2152:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2176:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2176b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2177:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2178f
	jmp 2179f
2178:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2179:
	test rdx, rdx
	jne 2177b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2180:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2180b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2181:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2182:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2183:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2184:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2185:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2185b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2184b
2186:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2187:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2188:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
2189:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 2189b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 2188b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2187b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2186b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2190:
	mov rbp, rdx
	and rbp, 7
	je 2191f
	jmp 2192f
2191:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2192:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2190b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov rsi, rax
	mov rax, QWORD PTR [rdi+280]
	mov rdx, rax
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
2193:
	movzx eax, BYTE PTR [rsi]
	movzx r9d, BYTE PTR [rdx]
	xor rax, r9
	or r8, rax
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2193b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+360]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 217f
216:
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
217:
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_dsa_validate_public_key_adx:
	mov r11, r8
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov eax, 0
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+304], rax
	mov QWORD PTR [r11+256], rdi
	mov QWORD PTR [r11+328], rdx
	mov QWORD PTR [r11+336], rcx
	mov QWORD PTR [r11+296], r8
	mov QWORD PTR [r11+312], rax
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [r11+256]
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+264], rax
	add rax, QWORD PTR [r11+336]
	mov QWORD PTR [r11+272], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+280], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+288], rax
	mov rdi, r11
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov QWORD PTR [rdi+176], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
	mov r9d, 0
25:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 26f
	jmp 27f
26:
	test rax, rax
	jne 28f
	jmp 29f
28:
	mov r8, rcx
	mov r9, rax
29:
27:
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov QWORD PTR [rdi+352], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rdx, QWORD PTR [rdi+176]
	cmp rdx, 128
	je 210f
	cmp rdx, 256
	je 212f
	cmp rdx, 384
	je 214f
	mov eax, 0
	jmp 215f
214:
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
215:
	jmp 213f
212:
	mov rax, r8
	xor rax, 28
	cmp rax, 1
	sbb rax, rax
	mov r10, rax
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
	or rax, r10
	mov r10, rax
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
	or rax, r10
213:
	jmp 211f
210:
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
211:
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	movzx eax, BYTE PTR [rsi+rcx*1-1]
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	movzx edx, BYTE PTR [rsi+rcx*1-1]
	and rax, rdx
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+344]
	mov rdx, QWORD PTR [rdi+352]
	cmp rdx, rax
	cmovb rax, rdx
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+360]
	test rax, rax
	je 216f
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 13312
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
223:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 224f
	jmp 225f
224:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
225:
	test rdx, rdx
	jne 223b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
229:
	test rdx, rdx
	jne 227b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
230:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 230b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
231:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 231b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
233:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 234f
	jmp 235f
234:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
235:
	test rdx, rdx
	jne 233b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
236:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 236b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
237:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 237b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 1
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
238:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 238b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
239:
	mov rbp, rdx
	and rbp, 7
	je 240f
	jmp 241f
240:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
241:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 239b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
242:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 243f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 245f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 247f
249:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 249b
	jmp 248f
247:
248:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
250:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
251:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
252:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 252b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
253:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 253b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
254:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 251b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
255:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 255b
	jmp 246f
245:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
256:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 256b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
257:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 257b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
258:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
259:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
260:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
261:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 258b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
262:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 262b
246:
	jmp 244f
243:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
263:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
264:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
265:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 265b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
266:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 266b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
267:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 264b
244:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
268:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
269:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 269b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
270:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 270b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
271:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 268b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
272:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
273:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 274f
276:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
277:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 277b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
278:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 278b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
279:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 276b
	jmp 275f
274:
275:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
280:
	mov rbp, rdx
	and rbp, 7
	je 281f
	jmp 282f
281:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
282:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 280b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14816
	mov rsi, rax
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
283:
	movzx eax, BYTE PTR [rsi]
	or r8, rax
	add rsi, 1
	sub rcx, 1
	jne 283b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 2
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
284:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 284b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
285:
	mov rbp, rdx
	and rbp, 7
	je 286f
	jmp 287f
286:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
287:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 285b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
288:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 288b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 289f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 291f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 293f
295:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 295b
	jmp 294f
293:
294:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
297:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
298:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 298b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
299:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 299b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2100:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 297b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2101:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2101b
	jmp 292f
291:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2102:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2103:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2103b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2104:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2105:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2105b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2106:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2107:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2104b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2108:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2108b
292:
	jmp 290f
289:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2109:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2110:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2111:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2112:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2113:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2110b
290:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2114:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2115:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2116f
	jmp 2117f
2116:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2117:
	test rdx, rdx
	jne 2115b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2118:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2118b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2119:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2120:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2121:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2122:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2123:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2122b
2124:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2125:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2126:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2126b
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	je 2127f
	mov r12, QWORD PTR [rdi+48]
	mov rax, r12
	add rax, 2
	mov rdx, QWORD PTR [rdi+216]
	imul rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+200]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2129:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	jmp 2128f
2127:
2128:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2125b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2124b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2130:
	mov rbp, rdx
	and rbp, 7
	je 2131f
	jmp 2132f
2131:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2132:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2130b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2133:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2134:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2135f
	jmp 2136f
2135:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2136:
	test rdx, rdx
	jne 2134b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r15, QWORD PTR [rbx]
	xor r15, 1
	mov r14, 1
2137:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2137b
	cmp r15, 1
	sbb rax, rax
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2138:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2139f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2141f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2143f
2145:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2145b
	jmp 2144f
2143:
2144:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2146:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2147:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2148:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2149:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2150:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2147b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2151:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2151b
	jmp 2142f
2141:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2152:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2153:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2153b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2154:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2155:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2155b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2156:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2157:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2154b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2158:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2158b
2142:
	jmp 2140f
2139:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2159:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2160:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2161:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2162:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2163:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2163b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2160b
2140:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2164:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2165:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2166f
	jmp 2167f
2166:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2167:
	test rdx, rdx
	jne 2165b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2168:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2169:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2170:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2170b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2171:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2172:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2173:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2172b
2174:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2175:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2176:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2176b
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	je 2177f
	mov r12, QWORD PTR [rdi+48]
	mov rax, r12
	add rax, 2
	mov rdx, QWORD PTR [rdi+216]
	imul rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+200]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2179:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2179b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	jmp 2178f
2177:
2178:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2175b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2174b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2180:
	mov rbp, rdx
	and rbp, 7
	je 2181f
	jmp 2182f
2181:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2182:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2180b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2183:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2184:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2185f
	jmp 2186f
2185:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2186:
	test rdx, rdx
	jne 2184b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r15, QWORD PTR [rbx]
	xor r15, 1
	mov r14, 1
2187:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2187b
	cmp r15, 1
	sbb rax, rax
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+360]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 217f
216:
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
217:
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_dsa_verify_prevalidated_adx:
	mov r11, QWORD PTR [rsp+24]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov eax, 0
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+304], rax
	mov QWORD PTR [r11+256], rdi
	mov QWORD PTR [r11+328], rdx
	mov QWORD PTR [r11+336], rcx
	mov QWORD PTR [r11+296], r8
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+312], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [r11+256]
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+264], rax
	add rax, QWORD PTR [r11+336]
	mov QWORD PTR [r11+272], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+280], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+288], rax
	mov rdi, r11
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov QWORD PTR [rdi+176], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
	mov r9d, 0
25:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 26f
	jmp 27f
26:
	test rax, rax
	jne 28f
	jmp 29f
28:
	mov r8, rcx
	mov r9, rax
29:
27:
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov QWORD PTR [rdi+352], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rdx, QWORD PTR [rdi+176]
	cmp rdx, 128
	je 210f
	cmp rdx, 256
	je 212f
	cmp rdx, 384
	je 214f
	mov eax, 0
	jmp 215f
214:
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
215:
	jmp 213f
212:
	mov rax, r8
	xor rax, 28
	cmp rax, 1
	sbb rax, rax
	mov r10, rax
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
	or rax, r10
	mov r10, rax
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
	or rax, r10
213:
	jmp 211f
210:
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
211:
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	movzx eax, BYTE PTR [rsi+rcx*1-1]
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	movzx edx, BYTE PTR [rsi+rcx*1-1]
	and rax, rdx
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+344]
	mov rdx, QWORD PTR [rdi+352]
	cmp rdx, rax
	cmovb rax, rdx
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+360]
	test rax, rax
	je 216f
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 13312
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
223:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 224f
	jmp 225f
224:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
225:
	test rdx, rdx
	jne 223b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 2
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
226:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 226b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
227:
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
229:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 227b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
230:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 230b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
231:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 232f
	jmp 233f
232:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
233:
	test rdx, rdx
	jne 231b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
234:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 234b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
235:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 235b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+296]
	add rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
236:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 236b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
237:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 238f
	jmp 239f
238:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
239:
	test rdx, rdx
	jne 237b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
240:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 240b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
241:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 241b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+296]
	add rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14784
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
242:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 243f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 245f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 247f
249:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 249b
	jmp 248f
247:
248:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
250:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
251:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
252:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 252b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
253:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 253b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
254:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 251b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
255:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 255b
	jmp 246f
245:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
256:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 256b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
257:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 257b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
258:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
259:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
260:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
261:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 258b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
262:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 262b
246:
	jmp 244f
243:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
263:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
264:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
265:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 265b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
266:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 266b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
267:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 264b
244:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
268:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 268b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
269:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 270f
	jmp 271f
270:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
271:
	test rdx, rdx
	jne 269b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
272:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
273:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
274:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 274b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
275:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 275b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
276:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
277:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 276b
278:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
279:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
280:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
281:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 281b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 280b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 279b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 278b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
282:
	mov rbp, rdx
	and rbp, 7
	je 283f
	jmp 284f
283:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
284:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 282b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14880
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
285:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 285b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 286f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 288f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 290f
292:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 292b
	jmp 291f
290:
291:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
293:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 293b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
294:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
295:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 295b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
296:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 296b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
297:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 294b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
298:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 298b
	jmp 289f
288:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
299:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 299b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2100:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2100b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2101:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2102:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2103:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2104:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2101b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2105:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2105b
289:
	jmp 287f
286:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2106:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2107:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2108:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2108b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2109:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2110:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2110b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2107b
287:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
2111:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2112:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2113:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2114:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2111b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2115:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2115b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2116:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2116b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 2117f
2119:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2120:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2121:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2122:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 2119b
	jmp 2118f
2117:
2118:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2123:
	mov rbp, rdx
	and rbp, 7
	je 2124f
	jmp 2125f
2124:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2125:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2123b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14880
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14784
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2126:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2127f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2129f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2131f
2133:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2133b
	jmp 2132f
2131:
2132:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2134:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2135:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2136:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2136b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2137:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2137b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2138:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2135b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2139:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2139b
	jmp 2130f
2129:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2140:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2140b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2141:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2141b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2142:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2143:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2143b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2144:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2145:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2145b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2142b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2146:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2146b
2130:
	jmp 2128f
2127:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2147:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2147b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2148:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2149:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2150:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2151:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2151b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2148b
2128:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2152:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2153:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2154f
	jmp 2155f
2154:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2155:
	test rdx, rdx
	jne 2153b
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2156:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+144]
	mov rcx, QWORD PTR [rax+152]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2157:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2158f
	jmp 2159f
2158:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2159:
	test rdx, rdx
	jne 2157b
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 5
	mov r8d, 1
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2160:
	mov rbp, rdx
	and rbp, 7
	je 2161f
	jmp 2162f
2161:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2162:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2160b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14784
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14848
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2163:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2163b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2164f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2166f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2168f
2170:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2170b
	jmp 2169f
2168:
2169:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2171:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2172:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2173:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2174:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2174b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2175:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2175b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2172b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2176:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2176b
	jmp 2167f
2166:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2177:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2177b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2178:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2178b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2179:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2180:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2180b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2181:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2182:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2179b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2183:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2183b
2167:
	jmp 2165f
2164:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2184:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2184b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2185:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2186:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2186b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2187:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2187b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2188:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2188b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2185b
2165:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2189:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2189b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2190:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2191f
	jmp 2192f
2191:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2192:
	test rdx, rdx
	jne 2190b
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2193:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2193b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+144]
	mov rcx, QWORD PTR [rax+152]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2194:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2195f
	jmp 2196f
2195:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2196:
	test rdx, rdx
	jne 2194b
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 5
	mov r8d, 1
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2197:
	mov rbp, rdx
	and rbp, 7
	je 2198f
	jmp 2199f
2198:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2199:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2197b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2200:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2200b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2201f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2203f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2205f
2207:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2207b
	jmp 2206f
2205:
2206:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2208:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2208b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2209:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2210:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2210b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2211:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2211b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2212:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2212b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2209b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2213:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2213b
	jmp 2204f
2203:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2214:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2214b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2215:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2215b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2216:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2217:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2217b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2218:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2218b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2219:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2219b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2216b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2220:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2220b
2204:
	jmp 2202f
2201:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2221:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2221b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2222:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2223:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2223b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2224:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2224b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2225:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2225b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2222b
2202:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2228f
	jmp 2229f
2228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2229:
	test rdx, rdx
	jne 2227b
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2230:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2230b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+144]
	mov rcx, QWORD PTR [rax+152]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2231:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2232f
	jmp 2233f
2232:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2233:
	test rdx, rdx
	jne 2231b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2234:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2234b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+120]
	mov r14, 0
2235:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2235b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2236:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2236b
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2237:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2237b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2238:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2238b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2239:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2239b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2240:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2240b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2241:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2241b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2242:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2242b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2243:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2243b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2244:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2244b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2245:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2245b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2246:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2246b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2247:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2247b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2248:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2248b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2249:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2249b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2250:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2250b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2251:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2251b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2252:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2252b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2253:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2253b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2254:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2254b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2255:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2255b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2256:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2256b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+120]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2257:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2257b
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2258:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2258b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rax, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rax+336]
	mov rdx, rax
	add rdx, 14816
	mov QWORD PTR [rdi+136], rdx
	mov rdx, rax
	add rdx, 14848
	mov QWORD PTR [rdi+176], rdx
	mov QWORD PTR [rdi+144], rcx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
2259:
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+136]
	mov rsi, QWORD PTR [rdi+176]
	movzx edx, BYTE PTR [rax+rcx*1]
	shl rdx, 8
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rdx
	mov QWORD PTR [rdi+168], rax
	mov eax, 4
	mov QWORD PTR [rdi+160], rax
2260:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rax, QWORD PTR [rdi+168]
	mov rdx, rax
	mov rcx, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 14
	and rdx, 3
	add rdx, rdx
	add rdx, rdx
	shr rcx, 6
	and rcx, 3
	add rdx, rcx
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2261:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
2262:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 2262b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 2261b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2260b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2259b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2263:
	mov rbp, rdx
	and rbp, 7
	je 2264f
	jmp 2265f
2264:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2265:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2263b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2266:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2266b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2267f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2269f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2271f
2273:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2273b
	jmp 2272f
2271:
2272:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2274:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2274b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2275:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2276:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2276b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2277:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2277b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2278:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2278b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2275b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2279:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2279b
	jmp 2270f
2269:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2280:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2280b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2281:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2281b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2282:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2283:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2283b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2284:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2284b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2285:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2285b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2282b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2286:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2286b
2270:
	jmp 2268f
2267:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2287:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2287b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2288:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2289:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2289b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2290:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2290b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2291:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2291b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2288b
2268:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
2292:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2293:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2293b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2294:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2294b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2295:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2295b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2292b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2297:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2297b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 2298f
2300:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2301:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2301b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2302:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2302b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2303:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2303b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 2300b
	jmp 2299f
2298:
2299:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2304:
	mov rbp, rdx
	and rbp, 7
	je 2305f
	jmp 2306f
2305:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2306:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2304b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14816
	mov rsi, rax
	mov rax, QWORD PTR [rdi+296]
	mov rdx, rax
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
2307:
	movzx eax, BYTE PTR [rsi]
	movzx r9d, BYTE PTR [rdx]
	xor rax, r9
	or r8, rax
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2307b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+360]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 217f
216:
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
217:
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_dsa_generate_key_adx:
	lea rsp, [rsp-248]
	mov QWORD PTR [rsp+40], rdi
	mov QWORD PTR [rsp+48], rsi
	mov QWORD PTR [rsp+56], rdx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], r8
	mov QWORD PTR [rsp+80], r9
	add rcx, r9
	mov QWORD PTR [rsp+168], rcx
	mov rax, 0
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+120], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+128], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+136], rax
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+72]
	mov rdx, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+88]
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	call {vg_dsa_check_parameters_adx}
	mov eax, eax
	cmp rax, 0
	je 20f
	mov rax, 0
	mov QWORD PTR [rsp+200], rax
	mov QWORD PTR [rsp+208], rax
	mov QWORD PTR [rsp+216], rax
	mov QWORD PTR [rsp+224], rax
	mov r10, QWORD PTR [rsp+168]
	mov r11, QWORD PTR [rsp+88]
	mov rsi, r10
	mov rcx, r11
	mov r8d, 0
	mov r9d, 0
22:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 23f
	jmp 24f
23:
	test rax, rax
	jne 25f
	jmp 26f
25:
	mov r8, rcx
	mov r9, rax
26:
24:
	add rsi, 1
	sub rcx, 1
	jne 22b
	sub r11, r8
	add r10, r11
	mov r11, r8
	mov rax, r9
	mov QWORD PTR [rsp+168], r10
	mov QWORD PTR [rsp+176], r11
	mov r9, rax
	mov r8, 255
	mov rcx, 127
	cmp rax, 128
	cmovb r8, rcx
	mov rcx, 63
	cmp rax, 64
	cmovb r8, rcx
	mov rcx, 31
	cmp rax, 32
	cmovb r8, rcx
	mov rcx, 15
	cmp rax, 16
	cmovb r8, rcx
	mov rcx, 7
	cmp rax, 8
	cmovb r8, rcx
	mov rcx, 3
	cmp rax, 4
	cmovb r8, rcx
	mov rcx, 1
	cmp rax, 2
	cmovb r8, rcx
	mov QWORD PTR [rsp+184], r8
	mov rax, 0
	mov rcx, 1
	cmp r11, 2
	cmovae rax, rcx
	cmp r9, 2
	cmovae rax, rcx
	cmp rax, 0
	je 27f
	mov rax, 128
	mov QWORD PTR [rsp+160], rax
	mov rax, 4
	mov QWORD PTR [rsp+192], rax
29:
	mov rax, QWORD PTR [rsp+120]
	sub rax, QWORD PTR [rsp+144]
	cmp rax, QWORD PTR [rsp+176]
	jb 210f
	mov r10, QWORD PTR [rsp+112]
	add r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+176]
	mov rdx, rsp
	add rdx, 200
	add rdx, QWORD PTR [rsp+88]
	sub rdx, r11
	movzx eax, BYTE PTR [r10]
	and rax, QWORD PTR [rsp+184]
	mov BYTE PTR [rdx], al
	add r10, 1
	add rdx, 1
	sub r11, 1
	jne 212f
	jmp 213f
212:
214:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [rdx], al
	add r10, 1
	add rdx, 1
	sub r11, 1
	jne 214b
213:
	mov rax, QWORD PTR [rsp+144]
	add rax, QWORD PTR [rsp+176]
	mov QWORD PTR [rsp+144], rax
	mov rdx, rsp
	add rdx, 200
	add rdx, QWORD PTR [rsp+88]
	mov r10, QWORD PTR [rsp+168]
	mov r11, QWORD PTR [rsp+176]
	add r10, r11
	mov r8, 0
	mov r9, 0
215:
	sub rdx, 1
	sub r10, 1
	movzx eax, BYTE PTR [rdx]
	or r9, rax
	movzx ecx, BYTE PTR [r10]
	add rcx, r8
	sub rax, rcx
	shr rax, 63
	mov r8, rax
	sub r11, 1
	jne 215b
	mov rax, 0
	test r9, r9
	cmove r8, rax
	test r8, r8
	jne 216f
	mov rax, QWORD PTR [rsp+160]
	sub rax, 1
	mov QWORD PTR [rsp+160], rax
	je 218f
	jmp 219f
218:
	mov QWORD PTR [rsp+192], rax
219:
	jmp 217f
216:
	mov rax, 1
	mov QWORD PTR [rsp+192], rax
217:
	jmp 211f
210:
	mov rax, 2
	mov QWORD PTR [rsp+192], rax
211:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 4
	je 29b
	mov rax, QWORD PTR [rsp+192]
	mov QWORD PTR [rsp+192], rax
	cmp rax, 1
	je 220f
	jmp 221f
220:
	mov rdi, QWORD PTR [rsp+40]
	mov rsi, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp+72]
	mov r8, QWORD PTR [rsp+80]
	mov r9, rsp
	add r9, 200
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+16], rax
	call {vg_dsa_derive_key_checked_adx}
	mov eax, eax
	mov QWORD PTR [rsp+192], rax
221:
	jmp 28f
27:
	mov QWORD PTR [rsp+192], rax
28:
	jmp 21f
20:
21:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 1
	jne 222f
	jmp 223f
222:
	mov r10, QWORD PTR [rsp+40]
	mov r11, QWORD PTR [rsp+48]
	mov rax, 0
224:
	mov BYTE PTR [r10], al
	add r10, 1
	sub r11, 1
	jne 224b
223:
	mov rax, 0
	mov QWORD PTR [rsp+200], rax
	mov QWORD PTR [rsp+208], rax
	mov QWORD PTR [rsp+216], rax
	mov QWORD PTR [rsp+224], rax
	mov rdx, QWORD PTR [rsp+56]
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+248]
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
	lea rsp, [rsp-264]
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
	lea rsp, [rsp+264]
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

vg_dsa_derive_key_adx:
	mov r11, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov eax, 0
	mov QWORD PTR [r11+296], rax
	mov QWORD PTR [r11+304], rax
	mov QWORD PTR [r11+312], rax
	mov QWORD PTR [r11+344], rax
	mov QWORD PTR [r11+320], rdi
	mov QWORD PTR [r11+256], rdx
	mov QWORD PTR [r11+328], r8
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [r11+256]
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+264], rax
	add rax, QWORD PTR [r11+336]
	mov QWORD PTR [r11+272], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+280], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+288], rax
	mov rdi, r11
	mov QWORD PTR [r11+288], r9
	mov rax, r11
	add rax, 15712
	mov QWORD PTR [r11+280], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov QWORD PTR [rdi+176], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
	mov r9d, 0
25:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 26f
	jmp 27f
26:
	test rax, rax
	jne 28f
	jmp 29f
28:
	mov r8, rcx
	mov r9, rax
29:
27:
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov QWORD PTR [rdi+352], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rdx, QWORD PTR [rdi+176]
	cmp rdx, 128
	je 210f
	cmp rdx, 256
	je 212f
	cmp rdx, 384
	je 214f
	mov eax, 0
	jmp 215f
214:
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
215:
	jmp 213f
212:
	mov rax, r8
	xor rax, 28
	cmp rax, 1
	sbb rax, rax
	mov r10, rax
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
	or rax, r10
	mov r10, rax
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
	or rax, r10
213:
	jmp 211f
210:
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
211:
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	movzx eax, BYTE PTR [rsi+rcx*1-1]
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	movzx edx, BYTE PTR [rsi+rcx*1-1]
	and rax, rdx
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+344]
	mov rdx, QWORD PTR [rdi+352]
	cmp rdx, rax
	cmovb rax, rdx
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+360]
	test rax, rax
	je 216f
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 13312
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
223:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 224f
	jmp 225f
224:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
225:
	test rdx, rdx
	jne 223b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
229:
	test rdx, rdx
	jne 227b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
230:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 230b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
231:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 231b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 15328
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 233f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 235f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 237f
239:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 239b
	jmp 238f
237:
238:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
240:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 240b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
241:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
242:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 242b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
243:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 243b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
244:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 244b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 241b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
245:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 245b
	jmp 236f
235:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
246:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 246b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
247:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 247b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
248:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
249:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 249b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
250:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
251:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 248b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
252:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 252b
236:
	jmp 234f
233:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
253:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 253b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
254:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
255:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 255b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
256:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 256b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
257:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 257b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 254b
234:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
258:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
259:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 260f
	jmp 261f
260:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
261:
	test rdx, rdx
	jne 259b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
262:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 262b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
263:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
264:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
265:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 265b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
266:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
267:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 266b
268:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
269:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
270:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
271:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 271b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 270b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 269b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 268b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
272:
	mov rbp, rdx
	and rbp, 7
	je 273f
	jmp 274f
273:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
274:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 272b
	mov rdi, QWORD PTR [rdi+128]
	mov rsi, rdi
	add rsi, 15328
	mov rdx, rdi
	add rdx, 15712
	mov rcx, QWORD PTR [rdi+328]
	mov r8, -1
275:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 275b
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
276:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 276b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
277:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 278f
	jmp 279f
278:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
279:
	test rdx, rdx
	jne 277b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
280:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 280b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
281:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 281b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
282:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 282b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
283:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 284f
	jmp 285f
284:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
285:
	test rdx, rdx
	jne 283b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
286:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 286b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
287:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 287b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 1
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
288:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 288b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
289:
	mov rbp, rdx
	and rbp, 7
	je 290f
	jmp 291f
290:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
291:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 289b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
292:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 292b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 293f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 295f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 297f
299:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 299b
	jmp 298f
297:
298:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2100:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2101:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2102:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2103:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2104:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2101b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2105:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2105b
	jmp 296f
295:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2106:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2107:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2107b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2108:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2109:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2110:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2110b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2111:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2108b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2112:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2112b
296:
	jmp 294f
293:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2113:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2114:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2115:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2115b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2116:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2116b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2117:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2117b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2114b
294:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
2118:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2119:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2120:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2121:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2118b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2122:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2123:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 2124f
2126:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2127:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2127b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2128:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2128b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2129:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 2126b
	jmp 2125f
2124:
2125:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2130:
	mov rbp, rdx
	and rbp, 7
	je 2131f
	jmp 2132f
2131:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2132:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2130b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14816
	mov rsi, rax
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
2133:
	movzx eax, BYTE PTR [rsi]
	or r8, rax
	add rsi, 1
	sub rcx, 1
	jne 2133b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 2
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
2134:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2135:
	mov rbp, rdx
	and rbp, 7
	je 2136f
	jmp 2137f
2136:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2137:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2135b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2138:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2139f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2141f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2143f
2145:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2145b
	jmp 2144f
2143:
2144:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2146:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2147:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2148:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2149:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2150:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2147b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2151:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2151b
	jmp 2142f
2141:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2152:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2153:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2153b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2154:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2155:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2155b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2156:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2157:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2154b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2158:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2158b
2142:
	jmp 2140f
2139:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2159:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2160:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2161:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2162:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2163:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2163b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2160b
2140:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2164:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2165:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2166f
	jmp 2167f
2166:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2167:
	test rdx, rdx
	jne 2165b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2168:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2169:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2170:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2170b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2171:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2172:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2173:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2172b
2174:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2175:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2176:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2176b
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	je 2177f
	mov r12, QWORD PTR [rdi+48]
	mov rax, r12
	add rax, 2
	mov rdx, QWORD PTR [rdi+216]
	imul rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+200]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2179:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2179b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	jmp 2178f
2177:
2178:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2175b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2174b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2180:
	mov rbp, rdx
	and rbp, 7
	je 2181f
	jmp 2182f
2181:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2182:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2180b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2183:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2184:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2185f
	jmp 2186f
2185:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2186:
	test rdx, rdx
	jne 2184b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r15, QWORD PTR [rbx]
	xor r15, 1
	mov r14, 1
2187:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2187b
	cmp r15, 1
	sbb rax, rax
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov r8, QWORD PTR [rdi+360]
	mov r13, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+280]
	mov r10, QWORD PTR [rdi+288]
	mov r11, QWORD PTR [rdi+328]
	mov r12, QWORD PTR [rdi+336]
	mov rdx, r13
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, r11
	add rcx, rcx
	add rcx, r12
2188:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2188b
	mov rdx, r13
	add rdx, r11
	add rdx, r11
	add rdx, r12
	mov rsi, r9
	mov rcx, r11
2189:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2189b
	mov rdx, r13
	add rdx, r11
	add rdx, r11
	add rdx, r11
	add rdx, r12
	mov rsi, r10
	mov rcx, r12
2190:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2190b
	mov rax, QWORD PTR [rdi+360]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 217f
216:
	mov rsi, QWORD PTR [rdi+320]
	mov rcx, QWORD PTR [rdi+328]
	add rcx, rcx
	add rcx, QWORD PTR [rdi+328]
	add rcx, QWORD PTR [rdi+336]
	add rcx, QWORD PTR [rdi+336]
	mov eax, 0
2191:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2191b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
217:
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_dsa_sign_random_prevalidated:
	lea rsp, [rsp-248]
	mov QWORD PTR [rsp+40], rdi
	mov QWORD PTR [rsp+48], rsi
	mov QWORD PTR [rsp+56], rdx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], r8
	mov QWORD PTR [rsp+80], r9
	add rcx, r9
	mov QWORD PTR [rsp+168], rcx
	mov rax, 0
	mov QWORD PTR [rsp+144], rax
	mov rax, 8
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+120], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+128], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+136], rax
	mov rax, 0
	mov QWORD PTR [rsp+200], rax
	mov QWORD PTR [rsp+208], rax
	mov QWORD PTR [rsp+216], rax
	mov QWORD PTR [rsp+224], rax
	mov r10, QWORD PTR [rsp+168]
	mov r11, QWORD PTR [rsp+88]
	mov rsi, r10
	mov rcx, r11
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	sub r11, r8
	add r10, r11
	mov r11, r8
	mov rax, r9
	mov QWORD PTR [rsp+168], r10
	mov QWORD PTR [rsp+176], r11
	mov r9, rax
	mov r8, 255
	mov rcx, 127
	cmp rax, 128
	cmovb r8, rcx
	mov rcx, 63
	cmp rax, 64
	cmovb r8, rcx
	mov rcx, 31
	cmp rax, 32
	cmovb r8, rcx
	mov rcx, 15
	cmp rax, 16
	cmovb r8, rcx
	mov rcx, 7
	cmp rax, 8
	cmovb r8, rcx
	mov rcx, 3
	cmp rax, 4
	cmovb r8, rcx
	mov rcx, 1
	cmp rax, 2
	cmovb r8, rcx
	mov QWORD PTR [rsp+184], r8
	mov rax, 0
	mov rcx, 1
	cmp r11, 2
	cmovae rax, rcx
	cmp r9, 2
	cmovae rax, rcx
	cmp rax, 0
	je 25f
27:
	mov rax, 128
	mov QWORD PTR [rsp+160], rax
	mov rax, 4
	mov QWORD PTR [rsp+192], rax
28:
	mov rax, QWORD PTR [rsp+120]
	sub rax, QWORD PTR [rsp+144]
	cmp rax, QWORD PTR [rsp+176]
	jb 29f
	mov r10, QWORD PTR [rsp+112]
	add r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+176]
	mov rdx, rsp
	add rdx, 200
	add rdx, QWORD PTR [rsp+88]
	sub rdx, r11
	movzx eax, BYTE PTR [r10]
	and rax, QWORD PTR [rsp+184]
	mov BYTE PTR [rdx], al
	add r10, 1
	add rdx, 1
	sub r11, 1
	jne 211f
	jmp 212f
211:
213:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [rdx], al
	add r10, 1
	add rdx, 1
	sub r11, 1
	jne 213b
212:
	mov rax, QWORD PTR [rsp+144]
	add rax, QWORD PTR [rsp+176]
	mov QWORD PTR [rsp+144], rax
	mov rdx, rsp
	add rdx, 200
	add rdx, QWORD PTR [rsp+88]
	mov r10, QWORD PTR [rsp+168]
	mov r11, QWORD PTR [rsp+176]
	add r10, r11
	mov r8, 0
	mov r9, 0
214:
	sub rdx, 1
	sub r10, 1
	movzx eax, BYTE PTR [rdx]
	or r9, rax
	movzx ecx, BYTE PTR [r10]
	add rcx, r8
	sub rax, rcx
	shr rax, 63
	mov r8, rax
	sub r11, 1
	jne 214b
	mov rax, 0
	test r9, r9
	cmove r8, rax
	test r8, r8
	jne 215f
	mov rax, QWORD PTR [rsp+160]
	sub rax, 1
	mov QWORD PTR [rsp+160], rax
	je 217f
	jmp 218f
217:
	mov QWORD PTR [rsp+192], rax
218:
	jmp 216f
215:
	mov rax, 1
	mov QWORD PTR [rsp+192], rax
216:
	jmp 210f
29:
	mov rax, 2
	mov QWORD PTR [rsp+192], rax
210:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 4
	je 28b
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 1
	je 219f
	jmp 220f
219:
	mov rdi, QWORD PTR [rsp+40]
	mov rsi, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp+72]
	mov r8, QWORD PTR [rsp+80]
	mov r9, rsp
	add r9, 200
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+32], rax
	call {vg_dsa_sign_prevalidated}
	mov eax, eax
	mov QWORD PTR [rsp+192], rax
	cmp rax, 0
	je 221f
	jmp 222f
221:
	mov rax, QWORD PTR [rsp+152]
	sub rax, 1
	mov QWORD PTR [rsp+152], rax
	jne 223f
	jmp 224f
223:
	mov rax, 4
	mov QWORD PTR [rsp+192], rax
224:
222:
220:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 4
	je 27b
	jmp 26f
25:
	mov QWORD PTR [rsp+192], rax
26:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 1
	jne 225f
	jmp 226f
225:
	mov r10, QWORD PTR [rsp+40]
	mov r11, QWORD PTR [rsp+48]
	mov rax, 0
227:
	mov BYTE PTR [r10], al
	add r10, 1
	sub r11, 1
	jne 227b
226:
	mov rax, 0
	mov QWORD PTR [rsp+200], rax
	mov QWORD PTR [rsp+208], rax
	mov QWORD PTR [rsp+216], rax
	mov QWORD PTR [rsp+224], rax
	mov rdx, QWORD PTR [rsp+56]
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+248]
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
	lea rsp, [rsp-264]
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
	lea rsp, [rsp+264]
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

vg_dsa_validate_private_key:
	mov r11, r8
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov eax, 0
	mov QWORD PTR [r11+296], rax
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+304], rax
	mov QWORD PTR [r11+312], rax
	mov QWORD PTR [r11+344], rax
	mov QWORD PTR [r11+256], rdi
	mov QWORD PTR [r11+328], rdx
	mov QWORD PTR [r11+336], rcx
	mov rax, QWORD PTR [r11+256]
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+264], rax
	add rax, QWORD PTR [r11+336]
	mov QWORD PTR [r11+272], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+280], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+288], rax
	mov rdi, r11
	mov rax, QWORD PTR [r11+288]
	mov QWORD PTR [r11+304], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov QWORD PTR [rdi+176], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
	mov r9d, 0
25:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 26f
	jmp 27f
26:
	test rax, rax
	jne 28f
	jmp 29f
28:
	mov r8, rcx
	mov r9, rax
29:
27:
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov QWORD PTR [rdi+352], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rdx, QWORD PTR [rdi+176]
	cmp rdx, 128
	je 210f
	cmp rdx, 256
	je 212f
	cmp rdx, 384
	je 214f
	mov eax, 0
	jmp 215f
214:
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
215:
	jmp 213f
212:
	mov rax, r8
	xor rax, 28
	cmp rax, 1
	sbb rax, rax
	mov r10, rax
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
	or rax, r10
	mov r10, rax
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
	or rax, r10
213:
	jmp 211f
210:
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
211:
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	movzx eax, BYTE PTR [rsi+rcx*1-1]
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	movzx edx, BYTE PTR [rsi+rcx*1-1]
	and rax, rdx
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+344]
	mov rdx, QWORD PTR [rdi+352]
	cmp rdx, rax
	cmovb rax, rdx
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+360]
	test rax, rax
	je 216f
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 13312
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
223:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 224f
	jmp 225f
224:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
225:
	test rdx, rdx
	jne 223b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
229:
	test rdx, rdx
	jne 227b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
230:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 230b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
231:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 231b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
233:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 234f
	jmp 235f
234:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
235:
	test rdx, rdx
	jne 233b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
236:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 236b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
237:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 237b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 1
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
238:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 238b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
239:
	mov rbp, rdx
	and rbp, 7
	je 240f
	jmp 241f
240:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
241:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 239b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
242:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 243f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 245f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 247f
249:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 249b
	jmp 248f
247:
248:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
250:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
251:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
252:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 252b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
253:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 253b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
254:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 251b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
255:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 255b
	jmp 246f
245:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
256:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 256b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
257:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 257b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
258:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
259:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
260:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
261:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 258b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
262:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 262b
246:
	jmp 244f
243:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
263:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
264:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
265:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 265b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
266:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 266b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
267:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 264b
244:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
268:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
269:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 269b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
270:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 270b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
271:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 268b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
272:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
273:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 274f
276:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
277:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 277b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
278:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 278b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
279:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 276b
	jmp 275f
274:
275:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
280:
	mov rbp, rdx
	and rbp, 7
	je 281f
	jmp 282f
281:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
282:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 280b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14816
	mov rsi, rax
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
283:
	movzx eax, BYTE PTR [rsi]
	or r8, rax
	add rsi, 1
	sub rcx, 1
	jne 283b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 2
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
284:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 284b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
285:
	mov rbp, rdx
	and rbp, 7
	je 286f
	jmp 287f
286:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
287:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 285b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
288:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 288b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 289f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 291f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 293f
295:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 295b
	jmp 294f
293:
294:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
297:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
298:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 298b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
299:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 299b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2100:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 297b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2101:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2101b
	jmp 292f
291:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2102:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2103:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2103b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2104:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2105:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2105b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2106:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2107:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2104b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2108:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2108b
292:
	jmp 290f
289:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2109:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2110:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2111:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2112:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2113:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2110b
290:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2114:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2115:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2116f
	jmp 2117f
2116:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2117:
	test rdx, rdx
	jne 2115b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2118:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2118b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2119:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2120:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2121:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2122:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2123:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2122b
2124:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2125:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2126:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2126b
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	je 2127f
	mov r12, QWORD PTR [rdi+48]
	mov rax, r12
	add rax, 2
	mov rdx, QWORD PTR [rdi+216]
	imul rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+200]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2129:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	jmp 2128f
2127:
2128:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2125b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2124b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2130:
	mov rbp, rdx
	and rbp, 7
	je 2131f
	jmp 2132f
2131:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2132:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2130b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2133:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2134:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2135f
	jmp 2136f
2135:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2136:
	test rdx, rdx
	jne 2134b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r15, QWORD PTR [rbx]
	xor r15, 1
	mov r14, 1
2137:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2137b
	cmp r15, 1
	sbb rax, rax
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2138:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2139:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2140f
	jmp 2141f
2140:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2141:
	test rdx, rdx
	jne 2139b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
2142:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2142b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
2143:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2143b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2144:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2145:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2146f
	jmp 2147f
2146:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2147:
	test rdx, rdx
	jne 2145b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
2148:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
2149:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2149b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2150:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2151f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2153f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2155f
2157:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2157b
	jmp 2156f
2155:
2156:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2158:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2158b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2159:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2160:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2160b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2161:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2162:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2159b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2163:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2163b
	jmp 2154f
2153:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2164:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2165:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2165b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2166:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2167:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2167b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2168:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2169:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2166b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2170:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2170b
2154:
	jmp 2152f
2151:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2171:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2172:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2173:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2174:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2174b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2175:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2175b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2172b
2152:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2176:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2176b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2177:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2178f
	jmp 2179f
2178:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2179:
	test rdx, rdx
	jne 2177b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2180:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2180b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2181:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2182:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2183:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2184:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2185:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2185b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2184b
2186:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2187:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2188:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
2189:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 2189b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 2188b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2187b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2186b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2190:
	mov rbp, rdx
	and rbp, 7
	je 2191f
	jmp 2192f
2191:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2192:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2190b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov rsi, rax
	mov rax, QWORD PTR [rdi+280]
	mov rdx, rax
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
2193:
	movzx eax, BYTE PTR [rsi]
	movzx r9d, BYTE PTR [rdx]
	xor rax, r9
	or r8, rax
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2193b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+360]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 217f
216:
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
217:
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_dsa_validate_public_key:
	mov r11, r8
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov eax, 0
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+304], rax
	mov QWORD PTR [r11+256], rdi
	mov QWORD PTR [r11+328], rdx
	mov QWORD PTR [r11+336], rcx
	mov QWORD PTR [r11+296], r8
	mov QWORD PTR [r11+312], rax
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [r11+256]
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+264], rax
	add rax, QWORD PTR [r11+336]
	mov QWORD PTR [r11+272], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+280], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+288], rax
	mov rdi, r11
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov QWORD PTR [rdi+176], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
	mov r9d, 0
25:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 26f
	jmp 27f
26:
	test rax, rax
	jne 28f
	jmp 29f
28:
	mov r8, rcx
	mov r9, rax
29:
27:
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov QWORD PTR [rdi+352], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rdx, QWORD PTR [rdi+176]
	cmp rdx, 128
	je 210f
	cmp rdx, 256
	je 212f
	cmp rdx, 384
	je 214f
	mov eax, 0
	jmp 215f
214:
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
215:
	jmp 213f
212:
	mov rax, r8
	xor rax, 28
	cmp rax, 1
	sbb rax, rax
	mov r10, rax
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
	or rax, r10
	mov r10, rax
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
	or rax, r10
213:
	jmp 211f
210:
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
211:
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	movzx eax, BYTE PTR [rsi+rcx*1-1]
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	movzx edx, BYTE PTR [rsi+rcx*1-1]
	and rax, rdx
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+344]
	mov rdx, QWORD PTR [rdi+352]
	cmp rdx, rax
	cmovb rax, rdx
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+360]
	test rax, rax
	je 216f
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 13312
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
223:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 224f
	jmp 225f
224:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
225:
	test rdx, rdx
	jne 223b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
229:
	test rdx, rdx
	jne 227b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
230:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 230b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
231:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 231b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
233:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 234f
	jmp 235f
234:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
235:
	test rdx, rdx
	jne 233b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
236:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 236b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
237:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 237b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 1
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
238:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 238b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
239:
	mov rbp, rdx
	and rbp, 7
	je 240f
	jmp 241f
240:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
241:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 239b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
242:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 243f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 245f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 247f
249:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 249b
	jmp 248f
247:
248:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
250:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
251:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
252:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 252b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
253:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 253b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
254:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 251b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
255:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 255b
	jmp 246f
245:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
256:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 256b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
257:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 257b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
258:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
259:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
260:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
261:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 258b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
262:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 262b
246:
	jmp 244f
243:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
263:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
264:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
265:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 265b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
266:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 266b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
267:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 264b
244:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
268:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
269:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 269b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
270:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 270b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
271:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 268b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
272:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
273:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 274f
276:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
277:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 277b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
278:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 278b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
279:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 276b
	jmp 275f
274:
275:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
280:
	mov rbp, rdx
	and rbp, 7
	je 281f
	jmp 282f
281:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
282:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 280b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14816
	mov rsi, rax
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
283:
	movzx eax, BYTE PTR [rsi]
	or r8, rax
	add rsi, 1
	sub rcx, 1
	jne 283b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 2
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
284:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 284b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
285:
	mov rbp, rdx
	and rbp, 7
	je 286f
	jmp 287f
286:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
287:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 285b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
288:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 288b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 289f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 291f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 293f
295:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 295b
	jmp 294f
293:
294:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
297:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
298:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 298b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
299:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 299b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2100:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 297b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2101:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2101b
	jmp 292f
291:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2102:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2103:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2103b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2104:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2105:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2105b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2106:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2107:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2104b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2108:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2108b
292:
	jmp 290f
289:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2109:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2110:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2111:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2112:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2113:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2110b
290:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2114:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2115:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2116f
	jmp 2117f
2116:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2117:
	test rdx, rdx
	jne 2115b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2118:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2118b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2119:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2120:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2121:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2122:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2123:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2122b
2124:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2125:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2126:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2126b
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	je 2127f
	mov r12, QWORD PTR [rdi+48]
	mov rax, r12
	add rax, 2
	mov rdx, QWORD PTR [rdi+216]
	imul rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+200]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2129:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	jmp 2128f
2127:
2128:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2125b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2124b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2130:
	mov rbp, rdx
	and rbp, 7
	je 2131f
	jmp 2132f
2131:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2132:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2130b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2133:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2134:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2135f
	jmp 2136f
2135:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2136:
	test rdx, rdx
	jne 2134b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r15, QWORD PTR [rbx]
	xor r15, 1
	mov r14, 1
2137:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2137b
	cmp r15, 1
	sbb rax, rax
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2138:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2139f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2141f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2143f
2145:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2145b
	jmp 2144f
2143:
2144:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2146:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2147:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2148:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2149:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2150:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2147b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2151:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2151b
	jmp 2142f
2141:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2152:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2153:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2153b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2154:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2155:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2155b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2156:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2157:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2154b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2158:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2158b
2142:
	jmp 2140f
2139:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2159:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2160:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2161:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2162:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2163:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2163b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2160b
2140:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2164:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2165:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2166f
	jmp 2167f
2166:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2167:
	test rdx, rdx
	jne 2165b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2168:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2169:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2170:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2170b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2171:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2172:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2173:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2172b
2174:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2175:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2176:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2176b
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	je 2177f
	mov r12, QWORD PTR [rdi+48]
	mov rax, r12
	add rax, 2
	mov rdx, QWORD PTR [rdi+216]
	imul rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+200]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2179:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2179b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	jmp 2178f
2177:
2178:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2175b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2174b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2180:
	mov rbp, rdx
	and rbp, 7
	je 2181f
	jmp 2182f
2181:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2182:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2180b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2183:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2184:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2185f
	jmp 2186f
2185:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2186:
	test rdx, rdx
	jne 2184b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r15, QWORD PTR [rbx]
	xor r15, 1
	mov r14, 1
2187:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2187b
	cmp r15, 1
	sbb rax, rax
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+360]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 217f
216:
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
217:
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_dsa_verify_prevalidated:
	mov r11, QWORD PTR [rsp+24]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov eax, 0
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+304], rax
	mov QWORD PTR [r11+256], rdi
	mov QWORD PTR [r11+328], rdx
	mov QWORD PTR [r11+336], rcx
	mov QWORD PTR [r11+296], r8
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+312], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [r11+256]
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+264], rax
	add rax, QWORD PTR [r11+336]
	mov QWORD PTR [r11+272], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+280], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+288], rax
	mov rdi, r11
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov QWORD PTR [rdi+176], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
	mov r9d, 0
25:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 26f
	jmp 27f
26:
	test rax, rax
	jne 28f
	jmp 29f
28:
	mov r8, rcx
	mov r9, rax
29:
27:
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov QWORD PTR [rdi+352], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rdx, QWORD PTR [rdi+176]
	cmp rdx, 128
	je 210f
	cmp rdx, 256
	je 212f
	cmp rdx, 384
	je 214f
	mov eax, 0
	jmp 215f
214:
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
215:
	jmp 213f
212:
	mov rax, r8
	xor rax, 28
	cmp rax, 1
	sbb rax, rax
	mov r10, rax
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
	or rax, r10
	mov r10, rax
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
	or rax, r10
213:
	jmp 211f
210:
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
211:
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	movzx eax, BYTE PTR [rsi+rcx*1-1]
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	movzx edx, BYTE PTR [rsi+rcx*1-1]
	and rax, rdx
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+344]
	mov rdx, QWORD PTR [rdi+352]
	cmp rdx, rax
	cmovb rax, rdx
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+360]
	test rax, rax
	je 216f
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 13312
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
223:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 224f
	jmp 225f
224:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
225:
	test rdx, rdx
	jne 223b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 2
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
226:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 226b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
227:
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
229:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 227b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
230:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 230b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
231:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 232f
	jmp 233f
232:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
233:
	test rdx, rdx
	jne 231b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
234:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 234b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
235:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 235b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+296]
	add rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
236:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 236b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
237:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 238f
	jmp 239f
238:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
239:
	test rdx, rdx
	jne 237b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
240:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 240b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
241:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 241b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+296]
	add rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14784
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
242:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 243f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 245f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 247f
249:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 249b
	jmp 248f
247:
248:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
250:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
251:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
252:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 252b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
253:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 253b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
254:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 251b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
255:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 255b
	jmp 246f
245:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
256:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 256b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
257:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 257b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
258:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
259:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
260:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
261:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 258b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
262:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 262b
246:
	jmp 244f
243:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
263:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
264:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
265:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 265b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
266:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 266b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
267:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 264b
244:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
268:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 268b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
269:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 270f
	jmp 271f
270:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
271:
	test rdx, rdx
	jne 269b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
272:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
273:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
274:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 274b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
275:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 275b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
276:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
277:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 276b
278:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
279:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
280:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
281:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 281b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 280b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 279b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 278b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
282:
	mov rbp, rdx
	and rbp, 7
	je 283f
	jmp 284f
283:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
284:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 282b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14880
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
285:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 285b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 286f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 288f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 290f
292:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 292b
	jmp 291f
290:
291:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
293:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 293b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
294:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
295:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 295b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
296:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 296b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
297:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 294b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
298:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 298b
	jmp 289f
288:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
299:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 299b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2100:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2100b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2101:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2102:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2103:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2104:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2101b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2105:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2105b
289:
	jmp 287f
286:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2106:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2107:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2108:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2108b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2109:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2110:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2110b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2107b
287:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
2111:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2112:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2113:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2114:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2111b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2115:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2115b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2116:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2116b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 2117f
2119:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2120:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2121:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2122:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 2119b
	jmp 2118f
2117:
2118:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2123:
	mov rbp, rdx
	and rbp, 7
	je 2124f
	jmp 2125f
2124:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2125:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2123b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14880
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14784
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2126:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2127f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2129f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2131f
2133:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2133b
	jmp 2132f
2131:
2132:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2134:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2135:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2136:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2136b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2137:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2137b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2138:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2135b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2139:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2139b
	jmp 2130f
2129:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2140:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2140b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2141:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2141b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2142:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2143:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2143b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2144:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2145:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2145b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2142b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2146:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2146b
2130:
	jmp 2128f
2127:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2147:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2147b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2148:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2149:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2150:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2151:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2151b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2148b
2128:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2152:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2153:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2154f
	jmp 2155f
2154:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2155:
	test rdx, rdx
	jne 2153b
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2156:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+144]
	mov rcx, QWORD PTR [rax+152]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2157:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2158f
	jmp 2159f
2158:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2159:
	test rdx, rdx
	jne 2157b
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov edx, 6
	mov ecx, 5
	mov r8d, 1
	call {vg_rsa_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2160:
	mov rbp, rdx
	and rbp, 7
	je 2161f
	jmp 2162f
2161:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2162:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2160b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14784
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14848
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2163:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2163b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2164f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2166f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2168f
2170:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2170b
	jmp 2169f
2168:
2169:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2171:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2172:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2173:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2174:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2174b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2175:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2175b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2172b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2176:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2176b
	jmp 2167f
2166:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2177:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2177b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2178:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2178b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2179:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2180:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2180b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2181:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2182:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2179b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2183:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2183b
2167:
	jmp 2165f
2164:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2184:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2184b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2185:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2186:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2186b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2187:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2187b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2188:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2188b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2185b
2165:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2189:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2189b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2190:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2191f
	jmp 2192f
2191:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2192:
	test rdx, rdx
	jne 2190b
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2193:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2193b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+144]
	mov rcx, QWORD PTR [rax+152]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2194:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2195f
	jmp 2196f
2195:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2196:
	test rdx, rdx
	jne 2194b
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov edx, 6
	mov ecx, 5
	mov r8d, 1
	call {vg_rsa_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2197:
	mov rbp, rdx
	and rbp, 7
	je 2198f
	jmp 2199f
2198:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2199:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2197b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2200:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2200b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2201f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2203f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2205f
2207:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2207b
	jmp 2206f
2205:
2206:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2208:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2208b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2209:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2210:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2210b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2211:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2211b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2212:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2212b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2209b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2213:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2213b
	jmp 2204f
2203:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2214:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2214b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2215:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2215b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2216:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2217:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2217b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2218:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2218b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2219:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2219b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2216b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2220:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2220b
2204:
	jmp 2202f
2201:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2221:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2221b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2222:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2223:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2223b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2224:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2224b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2225:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2225b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2222b
2202:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2228f
	jmp 2229f
2228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2229:
	test rdx, rdx
	jne 2227b
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2230:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2230b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+144]
	mov rcx, QWORD PTR [rax+152]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2231:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2232f
	jmp 2233f
2232:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2233:
	test rdx, rdx
	jne 2231b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2234:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2234b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+120]
	mov r14, 0
2235:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2235b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2236:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2236b
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2237:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2237b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2238:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2238b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2239:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2239b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2240:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2240b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2241:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2241b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2242:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2242b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2243:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2243b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2244:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2244b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2245:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2245b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2246:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2246b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2247:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2247b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2248:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2248b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2249:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2249b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2250:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2250b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2251:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2251b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2252:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2252b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2253:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2253b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2254:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2254b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2255:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2255b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2256:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2256b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+120]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2257:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2257b
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2258:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2258b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rax, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rax+336]
	mov rdx, rax
	add rdx, 14816
	mov QWORD PTR [rdi+136], rdx
	mov rdx, rax
	add rdx, 14848
	mov QWORD PTR [rdi+176], rdx
	mov QWORD PTR [rdi+144], rcx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
2259:
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+136]
	mov rsi, QWORD PTR [rdi+176]
	movzx edx, BYTE PTR [rax+rcx*1]
	shl rdx, 8
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rdx
	mov QWORD PTR [rdi+168], rax
	mov eax, 4
	mov QWORD PTR [rdi+160], rax
2260:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov rax, QWORD PTR [rdi+168]
	mov rdx, rax
	mov rcx, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 14
	and rdx, 3
	add rdx, rdx
	add rdx, rdx
	shr rcx, 6
	and rcx, 3
	add rdx, rcx
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2261:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
2262:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 2262b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 2261b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2260b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2259b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2263:
	mov rbp, rdx
	and rbp, 7
	je 2264f
	jmp 2265f
2264:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2265:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2263b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2266:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2266b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2267f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2269f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2271f
2273:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2273b
	jmp 2272f
2271:
2272:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2274:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2274b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2275:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2276:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2276b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2277:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2277b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2278:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2278b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2275b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2279:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2279b
	jmp 2270f
2269:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2280:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2280b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2281:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2281b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2282:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2283:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2283b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2284:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2284b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2285:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2285b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2282b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2286:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2286b
2270:
	jmp 2268f
2267:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2287:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2287b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2288:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2289:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2289b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2290:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2290b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2291:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2291b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2288b
2268:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
2292:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2293:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2293b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2294:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2294b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2295:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2295b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2292b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2297:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2297b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 2298f
2300:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2301:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2301b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2302:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2302b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2303:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2303b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 2300b
	jmp 2299f
2298:
2299:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2304:
	mov rbp, rdx
	and rbp, 7
	je 2305f
	jmp 2306f
2305:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2306:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2304b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14816
	mov rsi, rax
	mov rax, QWORD PTR [rdi+296]
	mov rdx, rax
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
2307:
	movzx eax, BYTE PTR [rsi]
	movzx r9d, BYTE PTR [rdx]
	xor rax, r9
	or r8, rax
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2307b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+360]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 217f
216:
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
217:
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_dsa_generate_key:
	lea rsp, [rsp-248]
	mov QWORD PTR [rsp+40], rdi
	mov QWORD PTR [rsp+48], rsi
	mov QWORD PTR [rsp+56], rdx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], r8
	mov QWORD PTR [rsp+80], r9
	add rcx, r9
	mov QWORD PTR [rsp+168], rcx
	mov rax, 0
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+120], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+128], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+136], rax
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+72]
	mov rdx, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+88]
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	call {vg_dsa_check_parameters}
	mov eax, eax
	cmp rax, 0
	je 20f
	mov rax, 0
	mov QWORD PTR [rsp+200], rax
	mov QWORD PTR [rsp+208], rax
	mov QWORD PTR [rsp+216], rax
	mov QWORD PTR [rsp+224], rax
	mov r10, QWORD PTR [rsp+168]
	mov r11, QWORD PTR [rsp+88]
	mov rsi, r10
	mov rcx, r11
	mov r8d, 0
	mov r9d, 0
22:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 23f
	jmp 24f
23:
	test rax, rax
	jne 25f
	jmp 26f
25:
	mov r8, rcx
	mov r9, rax
26:
24:
	add rsi, 1
	sub rcx, 1
	jne 22b
	sub r11, r8
	add r10, r11
	mov r11, r8
	mov rax, r9
	mov QWORD PTR [rsp+168], r10
	mov QWORD PTR [rsp+176], r11
	mov r9, rax
	mov r8, 255
	mov rcx, 127
	cmp rax, 128
	cmovb r8, rcx
	mov rcx, 63
	cmp rax, 64
	cmovb r8, rcx
	mov rcx, 31
	cmp rax, 32
	cmovb r8, rcx
	mov rcx, 15
	cmp rax, 16
	cmovb r8, rcx
	mov rcx, 7
	cmp rax, 8
	cmovb r8, rcx
	mov rcx, 3
	cmp rax, 4
	cmovb r8, rcx
	mov rcx, 1
	cmp rax, 2
	cmovb r8, rcx
	mov QWORD PTR [rsp+184], r8
	mov rax, 0
	mov rcx, 1
	cmp r11, 2
	cmovae rax, rcx
	cmp r9, 2
	cmovae rax, rcx
	cmp rax, 0
	je 27f
	mov rax, 128
	mov QWORD PTR [rsp+160], rax
	mov rax, 4
	mov QWORD PTR [rsp+192], rax
29:
	mov rax, QWORD PTR [rsp+120]
	sub rax, QWORD PTR [rsp+144]
	cmp rax, QWORD PTR [rsp+176]
	jb 210f
	mov r10, QWORD PTR [rsp+112]
	add r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+176]
	mov rdx, rsp
	add rdx, 200
	add rdx, QWORD PTR [rsp+88]
	sub rdx, r11
	movzx eax, BYTE PTR [r10]
	and rax, QWORD PTR [rsp+184]
	mov BYTE PTR [rdx], al
	add r10, 1
	add rdx, 1
	sub r11, 1
	jne 212f
	jmp 213f
212:
214:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [rdx], al
	add r10, 1
	add rdx, 1
	sub r11, 1
	jne 214b
213:
	mov rax, QWORD PTR [rsp+144]
	add rax, QWORD PTR [rsp+176]
	mov QWORD PTR [rsp+144], rax
	mov rdx, rsp
	add rdx, 200
	add rdx, QWORD PTR [rsp+88]
	mov r10, QWORD PTR [rsp+168]
	mov r11, QWORD PTR [rsp+176]
	add r10, r11
	mov r8, 0
	mov r9, 0
215:
	sub rdx, 1
	sub r10, 1
	movzx eax, BYTE PTR [rdx]
	or r9, rax
	movzx ecx, BYTE PTR [r10]
	add rcx, r8
	sub rax, rcx
	shr rax, 63
	mov r8, rax
	sub r11, 1
	jne 215b
	mov rax, 0
	test r9, r9
	cmove r8, rax
	test r8, r8
	jne 216f
	mov rax, QWORD PTR [rsp+160]
	sub rax, 1
	mov QWORD PTR [rsp+160], rax
	je 218f
	jmp 219f
218:
	mov QWORD PTR [rsp+192], rax
219:
	jmp 217f
216:
	mov rax, 1
	mov QWORD PTR [rsp+192], rax
217:
	jmp 211f
210:
	mov rax, 2
	mov QWORD PTR [rsp+192], rax
211:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 4
	je 29b
	mov rax, QWORD PTR [rsp+192]
	mov QWORD PTR [rsp+192], rax
	cmp rax, 1
	je 220f
	jmp 221f
220:
	mov rdi, QWORD PTR [rsp+40]
	mov rsi, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp+72]
	mov r8, QWORD PTR [rsp+80]
	mov r9, rsp
	add r9, 200
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+16], rax
	call {vg_dsa_derive_key_checked}
	mov eax, eax
	mov QWORD PTR [rsp+192], rax
221:
	jmp 28f
27:
	mov QWORD PTR [rsp+192], rax
28:
	jmp 21f
20:
21:
	mov rax, QWORD PTR [rsp+192]
	cmp rax, 1
	jne 222f
	jmp 223f
222:
	mov r10, QWORD PTR [rsp+40]
	mov r11, QWORD PTR [rsp+48]
	mov rax, 0
224:
	mov BYTE PTR [r10], al
	add r10, 1
	sub r11, 1
	jne 224b
223:
	mov rax, 0
	mov QWORD PTR [rsp+200], rax
	mov QWORD PTR [rsp+208], rax
	mov QWORD PTR [rsp+216], rax
	mov QWORD PTR [rsp+224], rax
	mov rdx, QWORD PTR [rsp+56]
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+248]
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
	lea rsp, [rsp-264]
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
	lea rsp, [rsp+264]
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

vg_dsa_derive_key:
	mov r11, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov eax, 0
	mov QWORD PTR [r11+296], rax
	mov QWORD PTR [r11+304], rax
	mov QWORD PTR [r11+312], rax
	mov QWORD PTR [r11+344], rax
	mov QWORD PTR [r11+320], rdi
	mov QWORD PTR [r11+256], rdx
	mov QWORD PTR [r11+328], r8
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [r11+256]
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+264], rax
	add rax, QWORD PTR [r11+336]
	mov QWORD PTR [r11+272], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+280], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+288], rax
	mov rdi, r11
	mov QWORD PTR [r11+288], r9
	mov rax, r11
	add rax, 15712
	mov QWORD PTR [r11+280], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov QWORD PTR [rdi+176], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
	mov r9d, 0
25:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 26f
	jmp 27f
26:
	test rax, rax
	jne 28f
	jmp 29f
28:
	mov r8, rcx
	mov r9, rax
29:
27:
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov QWORD PTR [rdi+352], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rdx, QWORD PTR [rdi+176]
	cmp rdx, 128
	je 210f
	cmp rdx, 256
	je 212f
	cmp rdx, 384
	je 214f
	mov eax, 0
	jmp 215f
214:
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
215:
	jmp 213f
212:
	mov rax, r8
	xor rax, 28
	cmp rax, 1
	sbb rax, rax
	mov r10, rax
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
	or rax, r10
	mov r10, rax
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
	or rax, r10
213:
	jmp 211f
210:
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
211:
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	movzx eax, BYTE PTR [rsi+rcx*1-1]
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	movzx edx, BYTE PTR [rsi+rcx*1-1]
	and rax, rdx
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+344]
	mov rdx, QWORD PTR [rdi+352]
	cmp rdx, rax
	cmovb rax, rdx
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+360]
	test rax, rax
	je 216f
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 13312
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
223:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 224f
	jmp 225f
224:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
225:
	test rdx, rdx
	jne 223b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
229:
	test rdx, rdx
	jne 227b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
230:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 230b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
231:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 231b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 15328
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 233f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 235f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 237f
239:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 239b
	jmp 238f
237:
238:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
240:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 240b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
241:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
242:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 242b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
243:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 243b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
244:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 244b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 241b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
245:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 245b
	jmp 236f
235:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
246:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 246b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
247:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 247b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
248:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
249:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 249b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
250:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
251:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 248b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
252:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 252b
236:
	jmp 234f
233:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
253:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 253b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
254:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
255:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 255b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
256:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 256b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
257:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 257b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 254b
234:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
258:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
259:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 260f
	jmp 261f
260:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
261:
	test rdx, rdx
	jne 259b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
262:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 262b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
263:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
264:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
265:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 265b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
266:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
267:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 266b
268:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
269:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
270:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
271:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 271b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 270b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 269b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 268b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
272:
	mov rbp, rdx
	and rbp, 7
	je 273f
	jmp 274f
273:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
274:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 272b
	mov rdi, QWORD PTR [rdi+128]
	mov rsi, rdi
	add rsi, 15328
	mov rdx, rdi
	add rdx, 15712
	mov rcx, QWORD PTR [rdi+328]
	mov r8, -1
275:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 275b
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
276:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 276b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
277:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 278f
	jmp 279f
278:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
279:
	test rdx, rdx
	jne 277b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
280:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 280b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
281:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 281b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
282:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 282b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
283:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 284f
	jmp 285f
284:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
285:
	test rdx, rdx
	jne 283b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
286:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 286b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
287:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 287b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 1
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
288:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 288b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
289:
	mov rbp, rdx
	and rbp, 7
	je 290f
	jmp 291f
290:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
291:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 289b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
292:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 292b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 293f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 295f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 297f
299:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 299b
	jmp 298f
297:
298:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2100:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2101:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2102:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2103:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2104:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2101b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2105:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2105b
	jmp 296f
295:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2106:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2107:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2107b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2108:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2109:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2110:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2110b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2111:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2108b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2112:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2112b
296:
	jmp 294f
293:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2113:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2114:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2115:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2115b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2116:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2116b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2117:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2117b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2114b
294:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
2118:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2119:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2120:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2121:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2118b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2122:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2123:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 2124f
2126:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2127:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2127b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2128:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2128b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2129:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 2126b
	jmp 2125f
2124:
2125:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2130:
	mov rbp, rdx
	and rbp, 7
	je 2131f
	jmp 2132f
2131:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2132:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2130b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14816
	mov rsi, rax
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
2133:
	movzx eax, BYTE PTR [rsi]
	or r8, rax
	add rsi, 1
	sub rcx, 1
	jne 2133b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 2
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
2134:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2135:
	mov rbp, rdx
	and rbp, 7
	je 2136f
	jmp 2137f
2136:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2137:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2135b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
2138:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 2139f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 2141f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2143f
2145:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2145b
	jmp 2144f
2143:
2144:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2146:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2147:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2148:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2149:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2150:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2147b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2151:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2151b
	jmp 2142f
2141:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2152:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2153:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2153b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2154:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2155:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2155b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2156:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2157:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2154b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2158:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2158b
2142:
	jmp 2140f
2139:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2159:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2160:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2161:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2162:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2163:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2163b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2160b
2140:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2164:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2165:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2166f
	jmp 2167f
2166:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2167:
	test rdx, rdx
	jne 2165b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2168:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2169:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2170:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2170b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2171:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2172:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2173:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2172b
2174:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2175:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2176:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul}
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2176b
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	je 2177f
	mov r12, QWORD PTR [rdi+48]
	mov rax, r12
	add rax, 2
	mov rdx, QWORD PTR [rdi+216]
	imul rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+200]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2179:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2179b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul}
	jmp 2178f
2177:
2178:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2175b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2174b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2180:
	mov rbp, rdx
	and rbp, 7
	je 2181f
	jmp 2182f
2181:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2182:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2180b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2183:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2184:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2185f
	jmp 2186f
2185:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2186:
	test rdx, rdx
	jne 2184b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r15, QWORD PTR [rbx]
	xor r15, 1
	mov r14, 1
2187:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2187b
	cmp r15, 1
	sbb rax, rax
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov r8, QWORD PTR [rdi+360]
	mov r13, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+280]
	mov r10, QWORD PTR [rdi+288]
	mov r11, QWORD PTR [rdi+328]
	mov r12, QWORD PTR [rdi+336]
	mov rdx, r13
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, r11
	add rcx, rcx
	add rcx, r12
2188:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2188b
	mov rdx, r13
	add rdx, r11
	add rdx, r11
	add rdx, r12
	mov rsi, r9
	mov rcx, r11
2189:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2189b
	mov rdx, r13
	add rdx, r11
	add rdx, r11
	add rdx, r11
	add rdx, r12
	mov rsi, r10
	mov rcx, r12
2190:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2190b
	mov rax, QWORD PTR [rdi+360]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 217f
216:
	mov rsi, QWORD PTR [rdi+320]
	mov rcx, QWORD PTR [rdi+328]
	add rcx, rcx
	add rcx, QWORD PTR [rdi+328]
	add rcx, QWORD PTR [rdi+336]
	add rcx, QWORD PTR [rdi+336]
	mov eax, 0
2191:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2191b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
217:
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_ifma:
	mov rax, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rax+8]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_3072_sha256_shani_mr_ifma}
	lea rsp, [rsp+56]
23:
21:
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
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-632]
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+632]
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
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_2048_sha256_shani_mr_ifma}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_1024_sha1_shani_mr_ifma}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6

vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_adx:
	mov rax, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rax+8]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_3072_sha256_shani_mr_adx}
	lea rsp, [rsp+56]
23:
21:
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
	lea rsp, [rsp-632]
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
	lea rsp, [rsp+632]
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
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_2048_sha256_shani_mr_adx}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_1024_sha1_shani_mr_adx}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6

vg_dsa_parameter_search_sha1_shani_sha256_shani:
	mov rax, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rax+8]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_3072_sha256_shani}
	lea rsp, [rsp+56]
23:
21:
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
	lea rsp, [rsp-632]
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
	lea rsp, [rsp+632]
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
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_2048_sha256_shani}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_1024_sha1_shani}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6

vg_dsa_parameter_search_sha1_avx_bmi_sha256_avx2_mr_ifma:
	mov rax, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rax+8]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_3072_sha256_avx2_mr_ifma}
	lea rsp, [rsp+56]
23:
21:
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
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-632]
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+632]
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
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_2048_sha256_avx2_mr_ifma}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_1024_sha1_avx_bmi_mr_ifma}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6

vg_dsa_parameter_search_sha1_avx_bmi_sha256_avx2_mr_adx:
	mov rax, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rax+8]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_3072_sha256_avx2_mr_adx}
	lea rsp, [rsp+56]
23:
21:
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
	lea rsp, [rsp-632]
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+632]
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
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_2048_sha256_avx2_mr_adx}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_1024_sha1_avx_bmi_mr_adx}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6

vg_dsa_parameter_search_sha1_avx_bmi_sha256_avx2:
	mov rax, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rax+8]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_3072_sha256_avx2}
	lea rsp, [rsp+56]
23:
21:
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
	lea rsp, [rsp-632]
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+632]
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
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_2048_sha256_avx2}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_1024_sha1_avx_bmi}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6

vg_dsa_parameter_search_mr_ifma:
	mov rax, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rax+8]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_3072_mr_ifma}
	lea rsp, [rsp+56]
23:
21:
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
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-632]
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+632]
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
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_2048_mr_ifma}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_1024_mr_ifma}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6

vg_dsa_parameter_search_mr_adx:
	mov rax, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rax+8]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_3072_mr_adx}
	lea rsp, [rsp+56]
23:
21:
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
	lea rsp, [rsp-632]
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
	lea rsp, [rsp+632]
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
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_2048_mr_adx}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_1024_mr_adx}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6

vg_dsa_parameter_search:
	mov rax, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rax+8]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_3072}
	lea rsp, [rsp+56]
23:
21:
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
	lea rsp, [rsp-632]
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
	lea rsp, [rsp+632]
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
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_parameter_search_1024}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6
