// The functions of `src/aes_xts.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt_unit_aesni:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_aesni:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt_aesni}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_to_aesni:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_encrypt_to_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 20f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 22f
24:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 24b
	jmp 23f
22:
23:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 21f
20:
	cmp rcx, 16
	jb 25f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 26f
25:
	cmp rcx, 8
	jb 27f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 28f
27:
	cmp rcx, 4
	jb 29f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 210f
29:
	mov r10d, 0
	cmp r10, rcx
	je 211f
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
210:
28:
26:
21:
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 214f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_to_aesni:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	sub r8, 1
	call {vg_aes_xts_decrypt_to_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	sub rax, 16
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 22f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 24f
26:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 26b
	jmp 25f
24:
25:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 23f
22:
	cmp rcx, 16
	jb 27f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 28f
27:
	cmp rcx, 8
	jb 29f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 210f
29:
	cmp rcx, 4
	jb 211f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 212f
211:
	mov r10d, 0
	cmp r10, rcx
	je 213f
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	jmp 214f
213:
214:
212:
210:
28:
23:
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_decrypt_to_aesni}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_aesni_pclmul:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_aesni_pclmul:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt_aesni_pclmul}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni_pclmul}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni_pclmul}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_to_aesni_pclmul:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_encrypt_to_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 20f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 22f
24:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 24b
	jmp 23f
22:
23:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 21f
20:
	cmp rcx, 16
	jb 25f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 26f
25:
	cmp rcx, 8
	jb 27f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 28f
27:
	cmp rcx, 4
	jb 29f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 210f
29:
	mov r10d, 0
	cmp r10, rcx
	je 211f
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
210:
28:
26:
21:
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 214f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_to_aesni_pclmul:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	sub r8, 1
	call {vg_aes_xts_decrypt_to_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	sub rax, 16
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 22f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 24f
26:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 26b
	jmp 25f
24:
25:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 23f
22:
	cmp rcx, 16
	jb 27f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 28f
27:
	cmp rcx, 8
	jb 29f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 210f
29:
	cmp rcx, 4
	jb 211f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 212f
211:
	mov r10d, 0
	cmp r10, rcx
	je 213f
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	jmp 214f
213:
214:
212:
210:
28:
23:
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni_pclmul}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_decrypt_to_aesni_pclmul}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_to:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_encrypt_to}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 20f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 22f
24:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 24b
	jmp 23f
22:
23:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 21f
20:
	cmp rcx, 16
	jb 25f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 26f
25:
	cmp rcx, 8
	jb 27f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 28f
27:
	cmp rcx, 4
	jb 29f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 210f
29:
	mov r10d, 0
	cmp r10, rcx
	je 211f
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
210:
28:
26:
21:
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 214f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt}
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_to:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	sub r8, 1
	call {vg_aes_xts_decrypt_to}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	sub rax, 16
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 22f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 24f
26:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 26b
	jmp 25f
24:
25:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 23f
22:
	cmp rcx, 16
	jb 27f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 28f
27:
	cmp rcx, 8
	jb 29f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 210f
29:
	cmp rcx, 4
	jb 211f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 212f
211:
	mov r10d, 0
	cmp r10, rcx
	je 213f
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	jmp 214f
213:
214:
212:
210:
28:
23:
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_decrypt_to}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_vaes:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_vaes:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt_vaes}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_to_vaes:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_encrypt_to_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 20f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 22f
24:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 24b
	jmp 23f
22:
23:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 21f
20:
	cmp rcx, 16
	jb 25f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 26f
25:
	cmp rcx, 8
	jb 27f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 28f
27:
	cmp rcx, 4
	jb 29f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 210f
29:
	mov r10d, 0
	cmp r10, rcx
	je 211f
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
210:
28:
26:
21:
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 214f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_to_vaes:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	sub r8, 1
	call {vg_aes_xts_decrypt_to_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	sub rax, 16
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 22f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 24f
26:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 26b
	jmp 25f
24:
25:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 23f
22:
	cmp rcx, 16
	jb 27f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 28f
27:
	cmp rcx, 8
	jb 29f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 210f
29:
	cmp rcx, 4
	jb 211f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 212f
211:
	mov r10d, 0
	cmp r10, rcx
	je 213f
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	jmp 214f
213:
214:
212:
210:
28:
23:
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_decrypt_to_vaes}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_vaes_vpclmul:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_vaes_vpclmul:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt_vaes_vpclmul}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_to_vaes_vpclmul:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_encrypt_to_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 20f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 22f
24:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 24b
	jmp 23f
22:
23:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 21f
20:
	cmp rcx, 16
	jb 25f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 26f
25:
	cmp rcx, 8
	jb 27f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 28f
27:
	cmp rcx, 4
	jb 29f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 210f
29:
	mov r10d, 0
	cmp r10, rcx
	je 211f
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
210:
28:
26:
21:
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 214f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_to_vaes_vpclmul:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	sub r8, 1
	call {vg_aes_xts_decrypt_to_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	sub rax, 16
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 22f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 24f
26:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 26b
	jmp 25f
24:
25:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 23f
22:
	cmp rcx, 16
	jb 27f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 28f
27:
	cmp rcx, 8
	jb 29f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 210f
29:
	cmp rcx, 4
	jb 211f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 212f
211:
	mov r10d, 0
	cmp r10, rcx
	je 213f
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	jmp 214f
213:
214:
212:
210:
28:
23:
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_decrypt_to_vaes_vpclmul}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul_avx512}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul_avx512}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul_avx512}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul_avx512}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt_vaes_vpclmul_avx512}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul_avx512}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul_avx512}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul_avx512}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_to_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul_avx512}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_encrypt_to_vaes_vpclmul_avx512}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 20f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 22f
24:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 24b
	jmp 23f
22:
23:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 21f
20:
	cmp rcx, 16
	jb 25f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 26f
25:
	cmp rcx, 8
	jb 27f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 28f
27:
	cmp rcx, 4
	jb 29f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 210f
29:
	mov r10d, 0
	cmp r10, rcx
	je 211f
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
210:
28:
26:
21:
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 214f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul_avx512}
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_to_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, QWORD PTR [rsp+8]
	mov r13, r9
	mov r14, r8
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul_avx512}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	sub r8, 1
	call {vg_aes_xts_decrypt_to_vaes_vpclmul_avx512}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	sub rax, 16
	mov rsi, r14
	add rsi, rax
	mov rdi, r12
	add rdi, rax
	mov rcx, r13
	sub rcx, rax
	cmp rcx, 32
	jb 22f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 24f
26:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 26b
	jmp 25f
24:
25:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 23f
22:
	cmp rcx, 16
	jb 27f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 28f
27:
	cmp rcx, 8
	jb 29f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 210f
29:
	cmp rcx, 4
	jb 211f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 212f
211:
	mov r10d, 0
	cmp r10, rcx
	je 213f
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	jmp 214f
213:
214:
212:
210:
28:
23:
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul_avx512}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
216:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 216b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul_avx512}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r14
	mov r8, r13
	shr r8, 4
	mov r9, r15
	mov r10, r12
	call {vg_aes_xts_decrypt_to_vaes_vpclmul_avx512}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6
