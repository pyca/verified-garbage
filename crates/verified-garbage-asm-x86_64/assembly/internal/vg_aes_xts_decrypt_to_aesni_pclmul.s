// The functions of `src/internal/vg_aes_xts_decrypt_to_aesni_pclmul.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_decrypt_to_aesni_pclmul:
	test r8, r8
	je 20f
	sub rcx, r10
	mov QWORD PTR [r9+248], rcx
	mov rcx, r10
	mov r11, rcx
	mov rax, r8
	mov r8, r9
	mov r9, rax
	mov rax, QWORD PTR [rdx]
	mov rcx, QWORD PTR [rdx+8]
	mov QWORD PTR [r8+256], rax
	mov QWORD PTR [r8+264], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+272], rax
	mov QWORD PTR [r8+280], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+288], rax
	mov QWORD PTR [r8+296], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+304], rax
	mov QWORD PTR [r8+312], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+320], rax
	mov QWORD PTR [r8+328], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+336], rax
	mov QWORD PTR [r8+344], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+352], rax
	mov QWORD PTR [r8+360], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+368], rax
	mov QWORD PTR [r8+376], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+16], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+32], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+48], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+64], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+80], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+96], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+112], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+128], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+144], xmm8
	cmp rsi, 10
	je 22f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+160], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+176], xmm8
	cmp rsi, 12
	je 24f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+192], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+208], xmm8
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	mov rcx, QWORD PTR [r8+248]
	cmp r9, 8
	jb 26f
	movabs rax, 135
	movq xmm11, rax
	mov rax, r8
	add rax, 256
28:
	movdqu xmm0, XMMWORD PTR [r11+rcx*1]
	movdqu xmm9, XMMWORD PTR [rax]
	pxor xmm0, xmm9
	movdqu xmm1, XMMWORD PTR [r11+rcx*1+16]
	movdqu xmm9, XMMWORD PTR [rax+16]
	pxor xmm1, xmm9
	movdqu xmm2, XMMWORD PTR [r11+rcx*1+32]
	movdqu xmm9, XMMWORD PTR [rax+32]
	pxor xmm2, xmm9
	movdqu xmm3, XMMWORD PTR [r11+rcx*1+48]
	movdqu xmm9, XMMWORD PTR [rax+48]
	pxor xmm3, xmm9
	movdqu xmm4, XMMWORD PTR [r11+rcx*1+64]
	movdqu xmm9, XMMWORD PTR [rax+64]
	pxor xmm4, xmm9
	movdqu xmm5, XMMWORD PTR [r11+rcx*1+80]
	movdqu xmm9, XMMWORD PTR [rax+80]
	pxor xmm5, xmm9
	movdqu xmm6, XMMWORD PTR [r11+rcx*1+96]
	movdqu xmm9, XMMWORD PTR [rax+96]
	pxor xmm6, xmm9
	movdqu xmm7, XMMWORD PTR [r11+rcx*1+112]
	movdqu xmm9, XMMWORD PTR [rax+112]
	pxor xmm7, xmm9
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	cmp rsi, 10
	je 29f
	cmp rsi, 12
	je 211f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	jmp 212f
211:
212:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	jmp 210f
29:
210:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	aesdeclast xmm2, xmm8
	aesdeclast xmm3, xmm8
	aesdeclast xmm4, xmm8
	aesdeclast xmm5, xmm8
	aesdeclast xmm6, xmm8
	aesdeclast xmm7, xmm8
	movdqu xmm9, XMMWORD PTR [rax]
	pxor xmm0, xmm9
	movdqu XMMWORD PTR [r11], xmm0
	movdqu xmm9, XMMWORD PTR [rax+16]
	pxor xmm1, xmm9
	movdqu XMMWORD PTR [r11+16], xmm1
	movdqu xmm9, XMMWORD PTR [rax+32]
	pxor xmm2, xmm9
	movdqu XMMWORD PTR [r11+32], xmm2
	movdqu xmm9, XMMWORD PTR [rax+48]
	pxor xmm3, xmm9
	movdqu XMMWORD PTR [r11+48], xmm3
	movdqu xmm9, XMMWORD PTR [rax+64]
	pxor xmm4, xmm9
	movdqu XMMWORD PTR [r11+64], xmm4
	movdqu xmm9, XMMWORD PTR [rax+80]
	pxor xmm5, xmm9
	movdqu XMMWORD PTR [r11+80], xmm5
	movdqu xmm9, XMMWORD PTR [rax+96]
	pxor xmm6, xmm9
	movdqu XMMWORD PTR [r11+96], xmm6
	movdqu xmm9, XMMWORD PTR [rax+112]
	pxor xmm7, xmm9
	movdqu XMMWORD PTR [r11+112], xmm7
	movdqu xmm9, XMMWORD PTR [rax]
	movdqa xmm10, xmm9
	psrldq xmm10, 15
	pclmulqdq xmm10, xmm11, 0
	pslldq xmm9, 1
	pxor xmm9, xmm10
	movdqu XMMWORD PTR [rax], xmm9
	movdqu xmm9, XMMWORD PTR [rax+16]
	movdqa xmm10, xmm9
	psrldq xmm10, 15
	pclmulqdq xmm10, xmm11, 0
	pslldq xmm9, 1
	pxor xmm9, xmm10
	movdqu XMMWORD PTR [rax+16], xmm9
	movdqu xmm9, XMMWORD PTR [rax+32]
	movdqa xmm10, xmm9
	psrldq xmm10, 15
	pclmulqdq xmm10, xmm11, 0
	pslldq xmm9, 1
	pxor xmm9, xmm10
	movdqu XMMWORD PTR [rax+32], xmm9
	movdqu xmm9, XMMWORD PTR [rax+48]
	movdqa xmm10, xmm9
	psrldq xmm10, 15
	pclmulqdq xmm10, xmm11, 0
	pslldq xmm9, 1
	pxor xmm9, xmm10
	movdqu XMMWORD PTR [rax+48], xmm9
	movdqu xmm9, XMMWORD PTR [rax+64]
	movdqa xmm10, xmm9
	psrldq xmm10, 15
	pclmulqdq xmm10, xmm11, 0
	pslldq xmm9, 1
	pxor xmm9, xmm10
	movdqu XMMWORD PTR [rax+64], xmm9
	movdqu xmm9, XMMWORD PTR [rax+80]
	movdqa xmm10, xmm9
	psrldq xmm10, 15
	pclmulqdq xmm10, xmm11, 0
	pslldq xmm9, 1
	pxor xmm9, xmm10
	movdqu XMMWORD PTR [rax+80], xmm9
	movdqu xmm9, XMMWORD PTR [rax+96]
	movdqa xmm10, xmm9
	psrldq xmm10, 15
	pclmulqdq xmm10, xmm11, 0
	pslldq xmm9, 1
	pxor xmm9, xmm10
	movdqu XMMWORD PTR [rax+96], xmm9
	movdqu xmm9, XMMWORD PTR [rax+112]
	movdqa xmm10, xmm9
	psrldq xmm10, 15
	pclmulqdq xmm10, xmm11, 0
	pslldq xmm9, 1
	pxor xmm9, xmm10
	movdqu XMMWORD PTR [rax+112], xmm9
	add r11, 128
	sub r9, 8
	cmp r9, 8
	jae 28b
	jmp 27f
26:
27:
	mov rax, r8
	add rax, 256
	test r9, r9
	je 213f
215:
	movdqu xmm0, XMMWORD PTR [r11+rcx*1]
	movdqu xmm9, XMMWORD PTR [rax]
	pxor xmm0, xmm9
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	cmp rsi, 10
	je 216f
	cmp rsi, 12
	je 218f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	jmp 219f
218:
219:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	jmp 217f
216:
217:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	movdqu xmm9, XMMWORD PTR [rax]
	pxor xmm0, xmm9
	movdqu XMMWORD PTR [r11], xmm0
	add r11, 16
	add rax, 16
	sub r9, 1
	jne 215b
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rdx], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rdx+8], rcx
	jmp 21f
20:
21:
	ret
	.p2align 6
