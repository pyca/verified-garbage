// The functions of `src/aes_siv.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_siv_init_aesni:
	lea rsp, [rsp-2568]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+160], rbx
	mov QWORD PTR [rcx+168], rbp
	mov QWORD PTR [rcx+176], r12
	mov QWORD PTR [rcx+184], r13
	mov QWORD PTR [rcx+192], r14
	mov rbx, rdi
	mov rbp, rsi
	shr rbp, 1
	mov r12, rdx
	mov r13, rcx
	mov r14, rsi
	shr r14, 3
	add r14, 6
	mov rsi, rbp
	add rcx, 256
	call {vg_aes_expand_key_scratch_aesni}
	mov rdi, r12
	mov rsi, r14
	mov rdx, r12
	add rdx, 240
	mov rcx, r13
	add rcx, 256
	call {vg_cmac_aes_subkeys_aesni}
	mov rdi, rbx
	add rdi, rbp
	mov rsi, rbp
	mov rdx, r12
	add rdx, 272
	mov rcx, r13
	add rcx, 256
	call {vg_aes_expand_key_scratch_aesni}
	mov rbx, QWORD PTR [r13+160]
	mov rbp, QWORD PTR [r13+168]
	mov r12, QWORD PTR [r13+176]
	mov r14, QWORD PTR [r13+192]
	mov r13, QWORD PTR [r13+184]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_siv_init:
	lea rsp, [rsp-2568]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+160], rbx
	mov QWORD PTR [rcx+168], rbp
	mov QWORD PTR [rcx+176], r12
	mov QWORD PTR [rcx+184], r13
	mov QWORD PTR [rcx+192], r14
	mov rbx, rdi
	mov rbp, rsi
	shr rbp, 1
	mov r12, rdx
	mov r13, rcx
	mov r14, rsi
	shr r14, 3
	add r14, 6
	mov rsi, rbp
	add rcx, 256
	call {vg_aes_expand_key_scratch}
	mov rdi, r12
	mov rsi, r14
	mov rdx, r12
	add rdx, 240
	mov rcx, r13
	add rcx, 256
	call {vg_cmac_aes_subkeys}
	mov rdi, rbx
	add rdi, rbp
	mov rsi, rbp
	mov rdx, r12
	add rdx, 272
	mov rcx, r13
	add rcx, 256
	call {vg_aes_expand_key_scratch}
	mov rbx, QWORD PTR [r13+160]
	mov rbp, QWORD PTR [r13+168]
	mov r12, QWORD PTR [r13+176]
	mov r14, QWORD PTR [r13+192]
	mov r13, QWORD PTR [r13+184]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_siv_init_vaes:
	lea rsp, [rsp-2568]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+160], rbx
	mov QWORD PTR [rcx+168], rbp
	mov QWORD PTR [rcx+176], r12
	mov QWORD PTR [rcx+184], r13
	mov QWORD PTR [rcx+192], r14
	mov rbx, rdi
	mov rbp, rsi
	shr rbp, 1
	mov r12, rdx
	mov r13, rcx
	mov r14, rsi
	shr r14, 3
	add r14, 6
	mov rsi, rbp
	add rcx, 256
	call {vg_aes_expand_key_scratch_aesni}
	mov rdi, r12
	mov rsi, r14
	mov rdx, r12
	add rdx, 240
	mov rcx, r13
	add rcx, 256
	call {vg_cmac_aes_subkeys_vaes}
	mov rdi, rbx
	add rdi, rbp
	mov rsi, rbp
	mov rdx, r12
	add rdx, 272
	mov rcx, r13
	add rcx, 256
	call {vg_aes_expand_key_scratch_aesni}
	mov rbx, QWORD PTR [r13+160]
	mov rbp, QWORD PTR [r13+168]
	mov r12, QWORD PTR [r13+176]
	mov r14, QWORD PTR [r13+192]
	mov r13, QWORD PTR [r13+184]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_siv_encrypt_aesni:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r15, rax
	mov r12, rax
	add r12, 2560
	mov r13, r8
	mov r14, r9
	mov QWORD PTR [r15+208], r13
	mov QWORD PTR [r15+216], r14
	mov QWORD PTR [r15+112], rdx
	mov QWORD PTR [r15+120], rcx
	mov rdx, r12
	mov rcx, r15
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+24], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rcx
	add r9, 256
	add rcx, 16
	mov r8d, 16
	call {vg_cmac_aes_finalize_aesni}
	mov rax, QWORD PTR [r15+120]
	test rax, rax
	je 20f
22:
	mov rax, QWORD PTR [r15+112]
	mov r13, QWORD PTR [rax]
	mov r14, QWORD PTR [rax+8]
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov ecx, 0
	test r14, r14
	je 23f
	mov rcx, r14
	sub rcx, 1
	mov rax, rcx
	and rax, 15
	sub rcx, rax
	jmp 24f
23:
24:
	mov r8, rcx
	shr r8, 4
	mov QWORD PTR [r15+144], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_aesni}
	mov rax, QWORD PTR [r15+144]
	mov rcx, r13
	add rcx, rax
	mov r8, r14
	sub r8, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
	mov QWORD PTR [r15+224], rbx
	mov rbx, r12
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r15+128]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r15+136]
	mov QWORD PTR [r12+8], rax
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+112]
	add rax, 16
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+120]
	sub rax, 1
	mov QWORD PTR [r15+120], rax
	jne 22b
	jmp 21f
20:
21:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	cmp r14, 16
	jb 25f
	cmp r14, 17
	jb 27f
	mov rcx, r14
	sub rcx, 1
	shr rcx, 4
	sub rcx, 1
	mov rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	jmp 28f
27:
	mov eax, 0
28:
	mov QWORD PTR [r15+144], rax
	add r13, rax
	mov rcx, r14
	sub rcx, rax
	mov rdx, r15
	add rdx, 32
	mov r11, rax
	mov r10d, 0
	test rcx, rcx
	je 29f
211:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	sub r13, r11
	mov rcx, r14
	sub rcx, r11
	add rcx, r15
	mov rax, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [rcx+16], rax
	mov rax, QWORD PTR [rcx+24]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [rcx+24], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov r8, QWORD PTR [r15+144]
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_aesni}
	mov r8d, 0
	cmp r14, 17
	jb 212f
	mov r8d, 1
	jmp 213f
212:
213:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r15
	add rcx, 32
	mov r9, r15
	add r9, 256
	mov QWORD PTR [r15+152], r8
	call {vg_cmac_aes_update_aesni}
	mov rax, QWORD PTR [r15+152]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov r8, r14
	sub r8, QWORD PTR [r15+144]
	sub r8, rax
	mov rcx, r15
	add rcx, 32
	add rcx, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
	jmp 26f
25:
	mov eax, 0
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rdx, r15
	add rdx, 32
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 214f
216:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
215:
	mov eax, 128
	mov BYTE PTR [r15+r14*1+32], al
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+144], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+152], rax
	mov QWORD PTR [r15+224], rbx
	mov rbx, r15
	mov rax, QWORD PTR [rbx+144]
	bswap rax
	mov rdx, QWORD PTR [rbx+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rdx
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+32]
	xor rax, QWORD PTR [r15+144]
	mov QWORD PTR [r15+32], rax
	mov rax, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+152]
	mov QWORD PTR [r15+40], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r15
	add rcx, 32
	mov r8d, 16
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
26:
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+64], rax
	mov rax, QWORD PTR [r15+8]
	movabs rdx, -549755814017
	and rax, rdx
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov r8, rcx
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_aesni}
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, rcx
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add r13, rcx
	sub r14, rcx
	je 217f
219:
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8d, 1
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_aesni}
	mov ecx, 16
	cmp r14, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, r14
221:
	mov r10d, 0
222:
	movzx eax, BYTE PTR [r13+r10*1]
	movzx edx, BYTE PTR [r15+r10*1+80]
	xor rax, rdx
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, 1
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add r13, 16
	sub r14, rcx
	jne 219b
	jmp 218f
217:
218:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	mov rax, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [rsp+16]
	mov r11, QWORD PTR [r10]
	mov QWORD PTR [rax], r11
	mov r11, QWORD PTR [r10+8]
	mov QWORD PTR [rax+8], r11
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_siv_decrypt_aesni:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r15, rax
	mov r12, rax
	add r12, 2560
	mov r13, r8
	mov r14, r9
	mov QWORD PTR [r15+208], r13
	mov QWORD PTR [r15+216], r14
	mov QWORD PTR [r15+112], rdx
	mov QWORD PTR [r15+120], rcx
	mov rdx, r12
	mov rcx, r15
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+24], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rcx
	add r9, 256
	add rcx, 16
	mov r8d, 16
	call {vg_cmac_aes_finalize_aesni}
	mov rax, QWORD PTR [r15+120]
	test rax, rax
	je 20f
22:
	mov rax, QWORD PTR [r15+112]
	mov r13, QWORD PTR [rax]
	mov r14, QWORD PTR [rax+8]
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov ecx, 0
	test r14, r14
	je 23f
	mov rcx, r14
	sub rcx, 1
	mov rax, rcx
	and rax, 15
	sub rcx, rax
	jmp 24f
23:
24:
	mov r8, rcx
	shr r8, 4
	mov QWORD PTR [r15+144], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_aesni}
	mov rax, QWORD PTR [r15+144]
	mov rcx, r13
	add rcx, rax
	mov r8, r14
	sub r8, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
	mov QWORD PTR [r15+224], rbx
	mov rbx, r12
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r15+128]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r15+136]
	mov QWORD PTR [r12+8], rax
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+112]
	add rax, 16
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+120]
	sub rax, 1
	mov QWORD PTR [r15+120], rax
	jne 22b
	jmp 21f
20:
21:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	mov rax, QWORD PTR [rsp+8]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [r15], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [r15+8], rcx
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+64], rax
	mov rax, QWORD PTR [r15+8]
	movabs rdx, -549755814017
	and rax, rdx
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov r8, rcx
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_aesni}
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, rcx
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add r13, rcx
	sub r14, rcx
	je 25f
27:
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8d, 1
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_aesni}
	mov ecx, 16
	cmp r14, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r14
29:
	mov r10d, 0
210:
	movzx eax, BYTE PTR [r13+r10*1]
	movzx edx, BYTE PTR [r15+r10*1+80]
	xor rax, rdx
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 210b
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, 1
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add r13, 16
	sub r14, rcx
	jne 27b
	jmp 26f
25:
26:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	cmp r14, 16
	jb 211f
	cmp r14, 17
	jb 213f
	mov rcx, r14
	sub rcx, 1
	shr rcx, 4
	sub rcx, 1
	mov rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	jmp 214f
213:
	mov eax, 0
214:
	mov QWORD PTR [r15+144], rax
	add r13, rax
	mov rcx, r14
	sub rcx, rax
	mov rdx, r15
	add rdx, 32
	mov r11, rax
	mov r10d, 0
	test rcx, rcx
	je 215f
217:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	jmp 216f
215:
216:
	sub r13, r11
	mov rcx, r14
	sub rcx, r11
	add rcx, r15
	mov rax, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [rcx+16], rax
	mov rax, QWORD PTR [rcx+24]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [rcx+24], rax
	mov eax, 0
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov r8, QWORD PTR [r15+144]
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_aesni}
	mov r8d, 0
	cmp r14, 17
	jb 218f
	mov r8d, 1
	jmp 219f
218:
219:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r15
	add rcx, 32
	mov r9, r15
	add r9, 256
	mov QWORD PTR [r15+152], r8
	call {vg_cmac_aes_update_aesni}
	mov rax, QWORD PTR [r15+152]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov r8, r14
	sub r8, QWORD PTR [r15+144]
	sub r8, rax
	mov rcx, r15
	add rcx, 32
	add rcx, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
	jmp 212f
211:
	mov eax, 0
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rdx, r15
	add rdx, 32
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 220f
222:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	jmp 221f
220:
221:
	mov eax, 128
	mov BYTE PTR [r15+r14*1+32], al
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+144], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+152], rax
	mov QWORD PTR [r15+224], rbx
	mov rbx, r15
	mov rax, QWORD PTR [rbx+144]
	bswap rax
	mov rdx, QWORD PTR [rbx+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rdx
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+32]
	xor rax, QWORD PTR [r15+144]
	mov QWORD PTR [r15+32], rax
	mov rax, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+152]
	mov QWORD PTR [r15+40], rax
	mov eax, 0
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r15
	add rcx, 32
	mov r8d, 16
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
212:
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+120]
	or rax, rdx
	mov rdx, rax
	sub rdx, 1
	mov rcx, rax
	xor rcx, -1
	and rcx, rdx
	mov rax, rcx
	shr rax, 63
	mov r11d, 0
	sub r11, rax
	mov QWORD PTR [r15+144], rax
	mov r10d, 0
	mov rcx, r14
	shr rcx, 3
	test rcx, rcx
	je 223f
225:
	mov rax, QWORD PTR [r13+r10*1]
	and rax, r11
	mov QWORD PTR [r13+r10*1], rax
	add r10, 8
	sub rcx, 1
	jne 225b
	jmp 224f
223:
224:
	cmp r10, r14
	je 226f
228:
	movzx eax, BYTE PTR [r13+r10*1]
	and rax, r11
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, r14
	jne 228b
	jmp 227f
226:
227:
	mov rax, QWORD PTR [r15+144]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_siv_encrypt_aesni_cbc:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r15, rax
	mov r12, rax
	add r12, 2560
	mov r13, r8
	mov r14, r9
	mov QWORD PTR [r15+208], r13
	mov QWORD PTR [r15+216], r14
	mov QWORD PTR [r15+112], rdx
	mov QWORD PTR [r15+120], rcx
	mov rdx, r12
	mov rcx, r15
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+24], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rcx
	add r9, 256
	add rcx, 16
	mov r8d, 16
	call {vg_cmac_aes_finalize_aesni}
	mov rax, QWORD PTR [r15+120]
	test rax, rax
	je 20f
22:
	mov rax, QWORD PTR [r15+112]
	mov r13, QWORD PTR [rax]
	mov r14, QWORD PTR [rax+8]
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov ecx, 0
	test r14, r14
	je 23f
	mov rcx, r14
	sub rcx, 1
	mov rax, rcx
	and rax, 15
	sub rcx, rax
	jmp 24f
23:
24:
	mov r8, rcx
	shr r8, 4
	mov QWORD PTR [r15+144], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_aesni_cbc}
	mov rax, QWORD PTR [r15+144]
	mov rcx, r13
	add rcx, rax
	mov r8, r14
	sub r8, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
	mov QWORD PTR [r15+224], rbx
	mov rbx, r12
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r15+128]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r15+136]
	mov QWORD PTR [r12+8], rax
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+112]
	add rax, 16
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+120]
	sub rax, 1
	mov QWORD PTR [r15+120], rax
	jne 22b
	jmp 21f
20:
21:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	cmp r14, 16
	jb 25f
	cmp r14, 17
	jb 27f
	mov rcx, r14
	sub rcx, 1
	shr rcx, 4
	sub rcx, 1
	mov rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	jmp 28f
27:
	mov eax, 0
28:
	mov QWORD PTR [r15+144], rax
	add r13, rax
	mov rcx, r14
	sub rcx, rax
	mov rdx, r15
	add rdx, 32
	mov r11, rax
	mov r10d, 0
	test rcx, rcx
	je 29f
211:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	sub r13, r11
	mov rcx, r14
	sub rcx, r11
	add rcx, r15
	mov rax, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [rcx+16], rax
	mov rax, QWORD PTR [rcx+24]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [rcx+24], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov r8, QWORD PTR [r15+144]
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_aesni_cbc}
	mov r8d, 0
	cmp r14, 17
	jb 212f
	mov r8d, 1
	jmp 213f
212:
213:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r15
	add rcx, 32
	mov r9, r15
	add r9, 256
	mov QWORD PTR [r15+152], r8
	call {vg_cmac_aes_update_aesni_cbc}
	mov rax, QWORD PTR [r15+152]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov r8, r14
	sub r8, QWORD PTR [r15+144]
	sub r8, rax
	mov rcx, r15
	add rcx, 32
	add rcx, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
	jmp 26f
25:
	mov eax, 0
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rdx, r15
	add rdx, 32
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 214f
216:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
215:
	mov eax, 128
	mov BYTE PTR [r15+r14*1+32], al
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+144], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+152], rax
	mov QWORD PTR [r15+224], rbx
	mov rbx, r15
	mov rax, QWORD PTR [rbx+144]
	bswap rax
	mov rdx, QWORD PTR [rbx+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rdx
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+32]
	xor rax, QWORD PTR [r15+144]
	mov QWORD PTR [r15+32], rax
	mov rax, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+152]
	mov QWORD PTR [r15+40], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r15
	add rcx, 32
	mov r8d, 16
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
26:
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+64], rax
	mov rax, QWORD PTR [r15+8]
	movabs rdx, -549755814017
	and rax, rdx
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov r8, rcx
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_aesni}
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, rcx
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add r13, rcx
	sub r14, rcx
	je 217f
219:
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8d, 1
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_aesni}
	mov ecx, 16
	cmp r14, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, r14
221:
	mov r10d, 0
222:
	movzx eax, BYTE PTR [r13+r10*1]
	movzx edx, BYTE PTR [r15+r10*1+80]
	xor rax, rdx
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, 1
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add r13, 16
	sub r14, rcx
	jne 219b
	jmp 218f
217:
218:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	mov rax, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [rsp+16]
	mov r11, QWORD PTR [r10]
	mov QWORD PTR [rax], r11
	mov r11, QWORD PTR [r10+8]
	mov QWORD PTR [rax+8], r11
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_siv_decrypt_aesni_cbc:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r15, rax
	mov r12, rax
	add r12, 2560
	mov r13, r8
	mov r14, r9
	mov QWORD PTR [r15+208], r13
	mov QWORD PTR [r15+216], r14
	mov QWORD PTR [r15+112], rdx
	mov QWORD PTR [r15+120], rcx
	mov rdx, r12
	mov rcx, r15
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+24], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rcx
	add r9, 256
	add rcx, 16
	mov r8d, 16
	call {vg_cmac_aes_finalize_aesni}
	mov rax, QWORD PTR [r15+120]
	test rax, rax
	je 20f
22:
	mov rax, QWORD PTR [r15+112]
	mov r13, QWORD PTR [rax]
	mov r14, QWORD PTR [rax+8]
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov ecx, 0
	test r14, r14
	je 23f
	mov rcx, r14
	sub rcx, 1
	mov rax, rcx
	and rax, 15
	sub rcx, rax
	jmp 24f
23:
24:
	mov r8, rcx
	shr r8, 4
	mov QWORD PTR [r15+144], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_aesni_cbc}
	mov rax, QWORD PTR [r15+144]
	mov rcx, r13
	add rcx, rax
	mov r8, r14
	sub r8, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
	mov QWORD PTR [r15+224], rbx
	mov rbx, r12
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r15+128]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r15+136]
	mov QWORD PTR [r12+8], rax
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+112]
	add rax, 16
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+120]
	sub rax, 1
	mov QWORD PTR [r15+120], rax
	jne 22b
	jmp 21f
20:
21:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	mov rax, QWORD PTR [rsp+8]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [r15], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [r15+8], rcx
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+64], rax
	mov rax, QWORD PTR [r15+8]
	movabs rdx, -549755814017
	and rax, rdx
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov r8, rcx
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_aesni}
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, rcx
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add r13, rcx
	sub r14, rcx
	je 25f
27:
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8d, 1
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_aesni}
	mov ecx, 16
	cmp r14, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r14
29:
	mov r10d, 0
210:
	movzx eax, BYTE PTR [r13+r10*1]
	movzx edx, BYTE PTR [r15+r10*1+80]
	xor rax, rdx
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 210b
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, 1
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add r13, 16
	sub r14, rcx
	jne 27b
	jmp 26f
25:
26:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	cmp r14, 16
	jb 211f
	cmp r14, 17
	jb 213f
	mov rcx, r14
	sub rcx, 1
	shr rcx, 4
	sub rcx, 1
	mov rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	jmp 214f
213:
	mov eax, 0
214:
	mov QWORD PTR [r15+144], rax
	add r13, rax
	mov rcx, r14
	sub rcx, rax
	mov rdx, r15
	add rdx, 32
	mov r11, rax
	mov r10d, 0
	test rcx, rcx
	je 215f
217:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	jmp 216f
215:
216:
	sub r13, r11
	mov rcx, r14
	sub rcx, r11
	add rcx, r15
	mov rax, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [rcx+16], rax
	mov rax, QWORD PTR [rcx+24]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [rcx+24], rax
	mov eax, 0
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov r8, QWORD PTR [r15+144]
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_aesni_cbc}
	mov r8d, 0
	cmp r14, 17
	jb 218f
	mov r8d, 1
	jmp 219f
218:
219:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r15
	add rcx, 32
	mov r9, r15
	add r9, 256
	mov QWORD PTR [r15+152], r8
	call {vg_cmac_aes_update_aesni_cbc}
	mov rax, QWORD PTR [r15+152]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov r8, r14
	sub r8, QWORD PTR [r15+144]
	sub r8, rax
	mov rcx, r15
	add rcx, 32
	add rcx, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
	jmp 212f
211:
	mov eax, 0
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rdx, r15
	add rdx, 32
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 220f
222:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	jmp 221f
220:
221:
	mov eax, 128
	mov BYTE PTR [r15+r14*1+32], al
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+144], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+152], rax
	mov QWORD PTR [r15+224], rbx
	mov rbx, r15
	mov rax, QWORD PTR [rbx+144]
	bswap rax
	mov rdx, QWORD PTR [rbx+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rdx
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+32]
	xor rax, QWORD PTR [r15+144]
	mov QWORD PTR [r15+32], rax
	mov rax, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+152]
	mov QWORD PTR [r15+40], rax
	mov eax, 0
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r15
	add rcx, 32
	mov r8d, 16
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_aesni}
212:
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+120]
	or rax, rdx
	mov rdx, rax
	sub rdx, 1
	mov rcx, rax
	xor rcx, -1
	and rcx, rdx
	mov rax, rcx
	shr rax, 63
	mov r11d, 0
	sub r11, rax
	mov QWORD PTR [r15+144], rax
	mov r10d, 0
	mov rcx, r14
	shr rcx, 3
	test rcx, rcx
	je 223f
225:
	mov rax, QWORD PTR [r13+r10*1]
	and rax, r11
	mov QWORD PTR [r13+r10*1], rax
	add r10, 8
	sub rcx, 1
	jne 225b
	jmp 224f
223:
224:
	cmp r10, r14
	je 226f
228:
	movzx eax, BYTE PTR [r13+r10*1]
	and rax, r11
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, r14
	jne 228b
	jmp 227f
226:
227:
	mov rax, QWORD PTR [r15+144]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_siv_encrypt:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r15, rax
	mov r12, rax
	add r12, 2560
	mov r13, r8
	mov r14, r9
	mov QWORD PTR [r15+208], r13
	mov QWORD PTR [r15+216], r14
	mov QWORD PTR [r15+112], rdx
	mov QWORD PTR [r15+120], rcx
	mov rdx, r12
	mov rcx, r15
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+24], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rcx
	add r9, 256
	add rcx, 16
	mov r8d, 16
	call {vg_cmac_aes_finalize}
	mov rax, QWORD PTR [r15+120]
	test rax, rax
	je 20f
22:
	mov rax, QWORD PTR [r15+112]
	mov r13, QWORD PTR [rax]
	mov r14, QWORD PTR [rax+8]
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov ecx, 0
	test r14, r14
	je 23f
	mov rcx, r14
	sub rcx, 1
	mov rax, rcx
	and rax, 15
	sub rcx, rax
	jmp 24f
23:
24:
	mov r8, rcx
	shr r8, 4
	mov QWORD PTR [r15+144], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update}
	mov rax, QWORD PTR [r15+144]
	mov rcx, r13
	add rcx, rax
	mov r8, r14
	sub r8, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize}
	mov QWORD PTR [r15+224], rbx
	mov rbx, r12
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r15+128]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r15+136]
	mov QWORD PTR [r12+8], rax
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+112]
	add rax, 16
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+120]
	sub rax, 1
	mov QWORD PTR [r15+120], rax
	jne 22b
	jmp 21f
20:
21:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	cmp r14, 16
	jb 25f
	cmp r14, 17
	jb 27f
	mov rcx, r14
	sub rcx, 1
	shr rcx, 4
	sub rcx, 1
	mov rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	jmp 28f
27:
	mov eax, 0
28:
	mov QWORD PTR [r15+144], rax
	add r13, rax
	mov rcx, r14
	sub rcx, rax
	mov rdx, r15
	add rdx, 32
	mov r11, rax
	mov r10d, 0
	test rcx, rcx
	je 29f
211:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	sub r13, r11
	mov rcx, r14
	sub rcx, r11
	add rcx, r15
	mov rax, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [rcx+16], rax
	mov rax, QWORD PTR [rcx+24]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [rcx+24], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov r8, QWORD PTR [r15+144]
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update}
	mov r8d, 0
	cmp r14, 17
	jb 212f
	mov r8d, 1
	jmp 213f
212:
213:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r15
	add rcx, 32
	mov r9, r15
	add r9, 256
	mov QWORD PTR [r15+152], r8
	call {vg_cmac_aes_update}
	mov rax, QWORD PTR [r15+152]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov r8, r14
	sub r8, QWORD PTR [r15+144]
	sub r8, rax
	mov rcx, r15
	add rcx, 32
	add rcx, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize}
	jmp 26f
25:
	mov eax, 0
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rdx, r15
	add rdx, 32
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 214f
216:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
215:
	mov eax, 128
	mov BYTE PTR [r15+r14*1+32], al
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+144], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+152], rax
	mov QWORD PTR [r15+224], rbx
	mov rbx, r15
	mov rax, QWORD PTR [rbx+144]
	bswap rax
	mov rdx, QWORD PTR [rbx+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rdx
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+32]
	xor rax, QWORD PTR [r15+144]
	mov QWORD PTR [r15+32], rax
	mov rax, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+152]
	mov QWORD PTR [r15+40], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r15
	add rcx, 32
	mov r8d, 16
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize}
26:
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+64], rax
	mov rax, QWORD PTR [r15+8]
	movabs rdx, -549755814017
	and rax, rdx
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov r8, rcx
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32}
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, rcx
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add r13, rcx
	sub r14, rcx
	je 217f
219:
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8d, 1
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32}
	mov ecx, 16
	cmp r14, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, r14
221:
	mov r10d, 0
222:
	movzx eax, BYTE PTR [r13+r10*1]
	movzx edx, BYTE PTR [r15+r10*1+80]
	xor rax, rdx
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, 1
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add r13, 16
	sub r14, rcx
	jne 219b
	jmp 218f
217:
218:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	mov rax, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [rsp+16]
	mov r11, QWORD PTR [r10]
	mov QWORD PTR [rax], r11
	mov r11, QWORD PTR [r10+8]
	mov QWORD PTR [rax+8], r11
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_siv_decrypt:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r15, rax
	mov r12, rax
	add r12, 2560
	mov r13, r8
	mov r14, r9
	mov QWORD PTR [r15+208], r13
	mov QWORD PTR [r15+216], r14
	mov QWORD PTR [r15+112], rdx
	mov QWORD PTR [r15+120], rcx
	mov rdx, r12
	mov rcx, r15
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+24], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rcx
	add r9, 256
	add rcx, 16
	mov r8d, 16
	call {vg_cmac_aes_finalize}
	mov rax, QWORD PTR [r15+120]
	test rax, rax
	je 20f
22:
	mov rax, QWORD PTR [r15+112]
	mov r13, QWORD PTR [rax]
	mov r14, QWORD PTR [rax+8]
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov ecx, 0
	test r14, r14
	je 23f
	mov rcx, r14
	sub rcx, 1
	mov rax, rcx
	and rax, 15
	sub rcx, rax
	jmp 24f
23:
24:
	mov r8, rcx
	shr r8, 4
	mov QWORD PTR [r15+144], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update}
	mov rax, QWORD PTR [r15+144]
	mov rcx, r13
	add rcx, rax
	mov r8, r14
	sub r8, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize}
	mov QWORD PTR [r15+224], rbx
	mov rbx, r12
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r15+128]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r15+136]
	mov QWORD PTR [r12+8], rax
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+112]
	add rax, 16
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+120]
	sub rax, 1
	mov QWORD PTR [r15+120], rax
	jne 22b
	jmp 21f
20:
21:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	mov rax, QWORD PTR [rsp+8]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [r15], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [r15+8], rcx
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+64], rax
	mov rax, QWORD PTR [r15+8]
	movabs rdx, -549755814017
	and rax, rdx
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov r8, rcx
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32}
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, rcx
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add r13, rcx
	sub r14, rcx
	je 25f
27:
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8d, 1
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32}
	mov ecx, 16
	cmp r14, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r14
29:
	mov r10d, 0
210:
	movzx eax, BYTE PTR [r13+r10*1]
	movzx edx, BYTE PTR [r15+r10*1+80]
	xor rax, rdx
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 210b
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, 1
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add r13, 16
	sub r14, rcx
	jne 27b
	jmp 26f
25:
26:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	cmp r14, 16
	jb 211f
	cmp r14, 17
	jb 213f
	mov rcx, r14
	sub rcx, 1
	shr rcx, 4
	sub rcx, 1
	mov rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	jmp 214f
213:
	mov eax, 0
214:
	mov QWORD PTR [r15+144], rax
	add r13, rax
	mov rcx, r14
	sub rcx, rax
	mov rdx, r15
	add rdx, 32
	mov r11, rax
	mov r10d, 0
	test rcx, rcx
	je 215f
217:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	jmp 216f
215:
216:
	sub r13, r11
	mov rcx, r14
	sub rcx, r11
	add rcx, r15
	mov rax, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [rcx+16], rax
	mov rax, QWORD PTR [rcx+24]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [rcx+24], rax
	mov eax, 0
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov r8, QWORD PTR [r15+144]
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update}
	mov r8d, 0
	cmp r14, 17
	jb 218f
	mov r8d, 1
	jmp 219f
218:
219:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r15
	add rcx, 32
	mov r9, r15
	add r9, 256
	mov QWORD PTR [r15+152], r8
	call {vg_cmac_aes_update}
	mov rax, QWORD PTR [r15+152]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov r8, r14
	sub r8, QWORD PTR [r15+144]
	sub r8, rax
	mov rcx, r15
	add rcx, 32
	add rcx, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize}
	jmp 212f
211:
	mov eax, 0
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rdx, r15
	add rdx, 32
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 220f
222:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	jmp 221f
220:
221:
	mov eax, 128
	mov BYTE PTR [r15+r14*1+32], al
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+144], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+152], rax
	mov QWORD PTR [r15+224], rbx
	mov rbx, r15
	mov rax, QWORD PTR [rbx+144]
	bswap rax
	mov rdx, QWORD PTR [rbx+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rdx
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+32]
	xor rax, QWORD PTR [r15+144]
	mov QWORD PTR [r15+32], rax
	mov rax, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+152]
	mov QWORD PTR [r15+40], rax
	mov eax, 0
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r15
	add rcx, 32
	mov r8d, 16
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize}
212:
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+120]
	or rax, rdx
	mov rdx, rax
	sub rdx, 1
	mov rcx, rax
	xor rcx, -1
	and rcx, rdx
	mov rax, rcx
	shr rax, 63
	mov r11d, 0
	sub r11, rax
	mov QWORD PTR [r15+144], rax
	mov r10d, 0
	mov rcx, r14
	shr rcx, 3
	test rcx, rcx
	je 223f
225:
	mov rax, QWORD PTR [r13+r10*1]
	and rax, r11
	mov QWORD PTR [r13+r10*1], rax
	add r10, 8
	sub rcx, 1
	jne 225b
	jmp 224f
223:
224:
	cmp r10, r14
	je 226f
228:
	movzx eax, BYTE PTR [r13+r10*1]
	and rax, r11
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, r14
	jne 228b
	jmp 227f
226:
227:
	mov rax, QWORD PTR [r15+144]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_siv_encrypt_vaes:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r15, rax
	mov r12, rax
	add r12, 2560
	mov r13, r8
	mov r14, r9
	mov QWORD PTR [r15+208], r13
	mov QWORD PTR [r15+216], r14
	mov QWORD PTR [r15+112], rdx
	mov QWORD PTR [r15+120], rcx
	mov rdx, r12
	mov rcx, r15
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+24], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rcx
	add r9, 256
	add rcx, 16
	mov r8d, 16
	call {vg_cmac_aes_finalize_vaes}
	mov rax, QWORD PTR [r15+120]
	test rax, rax
	je 20f
22:
	mov rax, QWORD PTR [r15+112]
	mov r13, QWORD PTR [rax]
	mov r14, QWORD PTR [rax+8]
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov ecx, 0
	test r14, r14
	je 23f
	mov rcx, r14
	sub rcx, 1
	mov rax, rcx
	and rax, 15
	sub rcx, rax
	jmp 24f
23:
24:
	mov r8, rcx
	shr r8, 4
	mov QWORD PTR [r15+144], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_vaes}
	mov rax, QWORD PTR [r15+144]
	mov rcx, r13
	add rcx, rax
	mov r8, r14
	sub r8, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_vaes}
	mov QWORD PTR [r15+224], rbx
	mov rbx, r12
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r15+128]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r15+136]
	mov QWORD PTR [r12+8], rax
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+112]
	add rax, 16
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+120]
	sub rax, 1
	mov QWORD PTR [r15+120], rax
	jne 22b
	jmp 21f
20:
21:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	cmp r14, 16
	jb 25f
	cmp r14, 17
	jb 27f
	mov rcx, r14
	sub rcx, 1
	shr rcx, 4
	sub rcx, 1
	mov rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	jmp 28f
27:
	mov eax, 0
28:
	mov QWORD PTR [r15+144], rax
	add r13, rax
	mov rcx, r14
	sub rcx, rax
	mov rdx, r15
	add rdx, 32
	mov r11, rax
	mov r10d, 0
	test rcx, rcx
	je 29f
211:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	sub r13, r11
	mov rcx, r14
	sub rcx, r11
	add rcx, r15
	mov rax, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [rcx+16], rax
	mov rax, QWORD PTR [rcx+24]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [rcx+24], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov r8, QWORD PTR [r15+144]
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_vaes}
	mov r8d, 0
	cmp r14, 17
	jb 212f
	mov r8d, 1
	jmp 213f
212:
213:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r15
	add rcx, 32
	mov r9, r15
	add r9, 256
	mov QWORD PTR [r15+152], r8
	call {vg_cmac_aes_update_vaes}
	mov rax, QWORD PTR [r15+152]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov r8, r14
	sub r8, QWORD PTR [r15+144]
	sub r8, rax
	mov rcx, r15
	add rcx, 32
	add rcx, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_vaes}
	jmp 26f
25:
	mov eax, 0
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rdx, r15
	add rdx, 32
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 214f
216:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
215:
	mov eax, 128
	mov BYTE PTR [r15+r14*1+32], al
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+144], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+152], rax
	mov QWORD PTR [r15+224], rbx
	mov rbx, r15
	mov rax, QWORD PTR [rbx+144]
	bswap rax
	mov rdx, QWORD PTR [rbx+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rdx
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+32]
	xor rax, QWORD PTR [r15+144]
	mov QWORD PTR [r15+32], rax
	mov rax, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+152]
	mov QWORD PTR [r15+40], rax
	mov eax, 0
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 0
	mov rcx, r15
	add rcx, 32
	mov r8d, 16
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_vaes}
26:
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+64], rax
	mov rax, QWORD PTR [r15+8]
	movabs rdx, -549755814017
	and rax, rdx
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov r8, rcx
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_vaes}
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, rcx
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add r13, rcx
	sub r14, rcx
	je 217f
219:
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8d, 1
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_vaes}
	mov ecx, 16
	cmp r14, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, r14
221:
	mov r10d, 0
222:
	movzx eax, BYTE PTR [r13+r10*1]
	movzx edx, BYTE PTR [r15+r10*1+80]
	xor rax, rdx
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, 1
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add r13, 16
	sub r14, rcx
	jne 219b
	jmp 218f
217:
218:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	mov rax, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [rsp+16]
	mov r11, QWORD PTR [r10]
	mov QWORD PTR [rax], r11
	mov r11, QWORD PTR [r10+8]
	mov QWORD PTR [rax+8], r11
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_siv_decrypt_vaes:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r15, rax
	mov r12, rax
	add r12, 2560
	mov r13, r8
	mov r14, r9
	mov QWORD PTR [r15+208], r13
	mov QWORD PTR [r15+216], r14
	mov QWORD PTR [r15+112], rdx
	mov QWORD PTR [r15+120], rcx
	mov rdx, r12
	mov rcx, r15
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+24], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rcx
	add r9, 256
	add rcx, 16
	mov r8d, 16
	call {vg_cmac_aes_finalize_vaes}
	mov rax, QWORD PTR [r15+120]
	test rax, rax
	je 20f
22:
	mov rax, QWORD PTR [r15+112]
	mov r13, QWORD PTR [rax]
	mov r14, QWORD PTR [rax+8]
	mov eax, 0
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov ecx, 0
	test r14, r14
	je 23f
	mov rcx, r14
	sub rcx, 1
	mov rax, rcx
	and rax, 15
	sub rcx, rax
	jmp 24f
23:
24:
	mov r8, rcx
	shr r8, 4
	mov QWORD PTR [r15+144], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_vaes}
	mov rax, QWORD PTR [r15+144]
	mov rcx, r13
	add rcx, rax
	mov r8, r14
	sub r8, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 128
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_vaes}
	mov QWORD PTR [r15+224], rbx
	mov rbx, r12
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r15+128]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r15+136]
	mov QWORD PTR [r12+8], rax
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+112]
	add rax, 16
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r15+120]
	sub rax, 1
	mov QWORD PTR [r15+120], rax
	jne 22b
	jmp 21f
20:
21:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	mov rax, QWORD PTR [rsp+8]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [r15], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [r15+8], rcx
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+64], rax
	mov rax, QWORD PTR [r15+8]
	movabs rdx, -549755814017
	and rax, rdx
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov r8, rcx
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_vaes}
	mov rcx, r14
	shr rcx, 4
	and rcx, 2147483647
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, rcx
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add r13, rcx
	sub r14, rcx
	je 25f
27:
	mov eax, 0
	mov QWORD PTR [r15+80], rax
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [r15+64]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+72]
	mov QWORD PTR [r15+104], rax
	mov rdi, rbx
	add rdi, 272
	mov rsi, rbp
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8d, 1
	mov r9, r15
	add r9, 256
	call {vg_aes_ctr32_vaes}
	mov ecx, 16
	cmp r14, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r14
29:
	mov r10d, 0
210:
	movzx eax, BYTE PTR [r13+r10*1]
	movzx edx, BYTE PTR [r15+r10*1+80]
	xor rax, rdx
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 210b
	mov rax, QWORD PTR [r15+72]
	bswap rax
	mov rdx, QWORD PTR [r15+64]
	bswap rdx
	add rax, 1
	adc rdx, 0
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+64], rdx
	mov QWORD PTR [r15+72], rax
	add r13, 16
	sub r14, rcx
	jne 27b
	jmp 26f
25:
26:
	mov r13, QWORD PTR [r15+208]
	mov r14, QWORD PTR [r15+216]
	cmp r14, 16
	jb 211f
	cmp r14, 17
	jb 213f
	mov rcx, r14
	sub rcx, 1
	shr rcx, 4
	sub rcx, 1
	mov rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	jmp 214f
213:
	mov eax, 0
214:
	mov QWORD PTR [r15+144], rax
	add r13, rax
	mov rcx, r14
	sub rcx, rax
	mov rdx, r15
	add rdx, 32
	mov r11, rax
	mov r10d, 0
	test rcx, rcx
	je 215f
217:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	jmp 216f
215:
216:
	sub r13, r11
	mov rcx, r14
	sub rcx, r11
	add rcx, r15
	mov rax, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [rcx+16], rax
	mov rax, QWORD PTR [rcx+24]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [rcx+24], rax
	mov eax, 0
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov r8, QWORD PTR [r15+144]
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r13
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_update_vaes}
	mov r8d, 0
	cmp r14, 17
	jb 218f
	mov r8d, 1
	jmp 219f
218:
219:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r15
	add rcx, 32
	mov r9, r15
	add r9, 256
	mov QWORD PTR [r15+152], r8
	call {vg_cmac_aes_update_vaes}
	mov rax, QWORD PTR [r15+152]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov r8, r14
	sub r8, QWORD PTR [r15+144]
	sub r8, rax
	mov rcx, r15
	add rcx, 32
	add rcx, rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_vaes}
	jmp 212f
211:
	mov eax, 0
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rdx, r15
	add rdx, 32
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 220f
222:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	jmp 221f
220:
221:
	mov eax, 128
	mov BYTE PTR [r15+r14*1+32], al
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+144], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+152], rax
	mov QWORD PTR [r15+224], rbx
	mov rbx, r15
	mov rax, QWORD PTR [rbx+144]
	bswap rax
	mov rdx, QWORD PTR [rbx+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rdx
	mov rbx, QWORD PTR [r15+224]
	mov rax, QWORD PTR [r15+32]
	xor rax, QWORD PTR [r15+144]
	mov QWORD PTR [r15+32], rax
	mov rax, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+152]
	mov QWORD PTR [r15+40], rax
	mov eax, 0
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 112
	mov rcx, r15
	add rcx, 32
	mov r8d, 16
	mov r9, r15
	add r9, 256
	call {vg_cmac_aes_finalize_vaes}
212:
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+120]
	or rax, rdx
	mov rdx, rax
	sub rdx, 1
	mov rcx, rax
	xor rcx, -1
	and rcx, rdx
	mov rax, rcx
	shr rax, 63
	mov r11d, 0
	sub r11, rax
	mov QWORD PTR [r15+144], rax
	mov r10d, 0
	mov rcx, r14
	shr rcx, 3
	test rcx, rcx
	je 223f
225:
	mov rax, QWORD PTR [r13+r10*1]
	and rax, r11
	mov QWORD PTR [r13+r10*1], rax
	add r10, 8
	sub rcx, 1
	jne 225b
	jmp 224f
223:
224:
	cmp r10, r14
	je 226f
228:
	movzx eax, BYTE PTR [r13+r10*1]
	and rax, r11
	mov BYTE PTR [r13+r10*1], al
	add r10, 1
	cmp r10, r14
	jne 228b
	jmp 227f
226:
227:
	mov rax, QWORD PTR [r15+144]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+2600]
	ret
	.p2align 6
