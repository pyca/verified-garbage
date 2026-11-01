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
