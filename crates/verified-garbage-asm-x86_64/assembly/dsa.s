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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-256]
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
	lea rsp, [rsp+256]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_dsa_validate_private_key_adx:
	lea rsp, [rsp-24]
	lea rax, {vg_rsa_mont_mul_adx}
	mov QWORD PTR [rsp], rax
	lea rax, {vg_rsa_lazy_mont_mul_adx}
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_validate_private_key_shared}
	lea rsp, [rsp+24]
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
	lea rsp, [rsp-32]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+32]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_dsa_validate_public_key_adx:
	lea rsp, [rsp-24]
	lea rax, {vg_rsa_mont_mul_adx}
	mov QWORD PTR [rsp], rax
	lea rax, {vg_rsa_lazy_mont_mul_adx}
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_validate_public_key_shared}
	lea rsp, [rsp+24]
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
	lea rsp, [rsp-32]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+32]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_dsa_verify_prevalidated_adx:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp+24], rax
	lea rax, {vg_rsa_mont_mul_adx}
	mov QWORD PTR [rsp+32], rax
	lea rax, {vg_rsa_lazy_mont_mul_adx}
	mov QWORD PTR [rsp+40], rax
	call {vg_dsa_verify_prevalidated_shared}
	lea rsp, [rsp+56]
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
	lea rsp, [rsp-64]
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+64]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-256]
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
	lea rsp, [rsp+256]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_dsa_derive_key_adx:
	lea rsp, [rsp-40]
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+16], rax
	lea rax, {vg_rsa_mont_mul_adx}
	mov QWORD PTR [rsp+24], rax
	lea rax, {vg_rsa_lazy_mont_mul_adx}
	mov QWORD PTR [rsp+32], rax
	call {vg_dsa_derive_key_shared}
	lea rsp, [rsp+40]
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
	lea rsp, [rsp-48]
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+48]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-256]
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
	lea rsp, [rsp+256]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_dsa_validate_private_key:
	lea rsp, [rsp-24]
	lea rax, {vg_rsa_mont_mul}
	mov QWORD PTR [rsp], rax
	lea rax, {vg_rsa_lazy_mont_mul}
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_validate_private_key_shared}
	lea rsp, [rsp+24]
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
	lea rsp, [rsp-32]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+32]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_dsa_validate_public_key:
	lea rsp, [rsp-24]
	lea rax, {vg_rsa_mont_mul}
	mov QWORD PTR [rsp], rax
	lea rax, {vg_rsa_lazy_mont_mul}
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_validate_public_key_shared}
	lea rsp, [rsp+24]
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
	lea rsp, [rsp-32]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+32]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_dsa_verify_prevalidated:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp+24], rax
	lea rax, {vg_rsa_mont_mul}
	mov QWORD PTR [rsp+32], rax
	lea rax, {vg_rsa_lazy_mont_mul}
	mov QWORD PTR [rsp+40], rax
	call {vg_dsa_verify_prevalidated_shared}
	lea rsp, [rsp+56]
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
	lea rsp, [rsp-64]
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+64]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-256]
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
	lea rsp, [rsp+256]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_dsa_derive_key:
	lea rsp, [rsp-40]
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+16], rax
	lea rax, {vg_rsa_mont_mul}
	mov QWORD PTR [rsp+24], rax
	lea rax, {vg_rsa_lazy_mont_mul}
	mov QWORD PTR [rsp+32], rax
	call {vg_dsa_derive_key_shared}
	lea rsp, [rsp+40]
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
	lea rsp, [rsp-48]
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+48]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
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
	lea rax, {vg_sha256_update_scratch_shani}
	lea r10, {vg_sha256_finalize_scratch_shani}
	lea r11, {vg_dsa_probable_prime_ifma}
	call {vg_dsa_parameter_search_3072}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-624]
	vmovdqu YMMWORD PTR [rsp+592], ymm0
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
	lea rsp, [rsp+624]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha256_update_scratch_shani}
	lea r10, {vg_sha256_finalize_scratch_shani}
	lea r11, {vg_dsa_probable_prime_ifma}
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha1_update_scratch_shani}
	lea r10, {vg_sha1_finalize_scratch_shani}
	lea r11, {vg_dsa_probable_prime_ifma}
	call {vg_dsa_parameter_search_1024}
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
	lea rax, {vg_sha256_update_scratch_shani}
	lea r10, {vg_sha256_finalize_scratch_shani}
	lea r11, {vg_dsa_probable_prime_adx}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-624]
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
	lea rsp, [rsp+624]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha256_update_scratch_shani}
	lea r10, {vg_sha256_finalize_scratch_shani}
	lea r11, {vg_dsa_probable_prime_adx}
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha1_update_scratch_shani}
	lea r10, {vg_sha1_finalize_scratch_shani}
	lea r11, {vg_dsa_probable_prime_adx}
	call {vg_dsa_parameter_search_1024}
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
	lea rax, {vg_sha256_update_scratch_shani}
	lea r10, {vg_sha256_finalize_scratch_shani}
	lea r11, {vg_dsa_probable_prime}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-624]
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
	lea rsp, [rsp+624]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha256_update_scratch_shani}
	lea r10, {vg_sha256_finalize_scratch_shani}
	lea r11, {vg_dsa_probable_prime}
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha1_update_scratch_shani}
	lea r10, {vg_sha1_finalize_scratch_shani}
	lea r11, {vg_dsa_probable_prime}
	call {vg_dsa_parameter_search_1024}
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
	lea rax, {vg_sha256_update_scratch_avx2}
	lea r10, {vg_sha256_finalize_scratch_avx2}
	lea r11, {vg_dsa_probable_prime_ifma}
	call {vg_dsa_parameter_search_3072}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-624]
	vmovdqu YMMWORD PTR [rsp+592], ymm0
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
	lea rsp, [rsp+624]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha256_update_scratch_avx2}
	lea r10, {vg_sha256_finalize_scratch_avx2}
	lea r11, {vg_dsa_probable_prime_ifma}
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha1_update_scratch_avx_bmi}
	lea r10, {vg_sha1_finalize_scratch_avx_bmi}
	lea r11, {vg_dsa_probable_prime_ifma}
	call {vg_dsa_parameter_search_1024}
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
	lea rax, {vg_sha256_update_scratch_avx2}
	lea r10, {vg_sha256_finalize_scratch_avx2}
	lea r11, {vg_dsa_probable_prime_adx}
	call {vg_dsa_parameter_search_3072}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-624]
	vmovdqu YMMWORD PTR [rsp+592], ymm0
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
	lea rsp, [rsp+624]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha256_update_scratch_avx2}
	lea r10, {vg_sha256_finalize_scratch_avx2}
	lea r11, {vg_dsa_probable_prime_adx}
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha1_update_scratch_avx_bmi}
	lea r10, {vg_sha1_finalize_scratch_avx_bmi}
	lea r11, {vg_dsa_probable_prime_adx}
	call {vg_dsa_parameter_search_1024}
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
	lea rax, {vg_sha256_update_scratch_avx2}
	lea r10, {vg_sha256_finalize_scratch_avx2}
	lea r11, {vg_dsa_probable_prime}
	call {vg_dsa_parameter_search_3072}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-624]
	vmovdqu YMMWORD PTR [rsp+592], ymm0
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
	lea rsp, [rsp+624]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha256_update_scratch_avx2}
	lea r10, {vg_sha256_finalize_scratch_avx2}
	lea r11, {vg_dsa_probable_prime}
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha1_update_scratch_avx_bmi}
	lea r10, {vg_sha1_finalize_scratch_avx_bmi}
	lea r11, {vg_dsa_probable_prime}
	call {vg_dsa_parameter_search_1024}
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
	lea rax, {vg_sha256_update_scratch}
	lea r10, {vg_sha256_finalize_scratch}
	lea r11, {vg_dsa_probable_prime_ifma}
	call {vg_dsa_parameter_search_3072}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-624]
	vmovdqu YMMWORD PTR [rsp+592], ymm0
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
	lea rsp, [rsp+624]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha256_update_scratch}
	lea r10, {vg_sha256_finalize_scratch}
	lea r11, {vg_dsa_probable_prime_ifma}
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha1_update_scratch}
	lea r10, {vg_sha1_finalize_scratch}
	lea r11, {vg_dsa_probable_prime_ifma}
	call {vg_dsa_parameter_search_1024}
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
	lea rax, {vg_sha256_update_scratch}
	lea r10, {vg_sha256_finalize_scratch}
	lea r11, {vg_dsa_probable_prime_adx}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-624]
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
	lea rsp, [rsp+624]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha256_update_scratch}
	lea r10, {vg_sha256_finalize_scratch}
	lea r11, {vg_dsa_probable_prime_adx}
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha1_update_scratch}
	lea r10, {vg_sha1_finalize_scratch}
	lea r11, {vg_dsa_probable_prime_adx}
	call {vg_dsa_parameter_search_1024}
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
	lea rax, {vg_sha256_update_scratch}
	lea r10, {vg_sha256_finalize_scratch}
	lea r11, {vg_dsa_probable_prime}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-624]
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
	lea rsp, [rsp+624]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
22:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha256_update_scratch}
	lea r10, {vg_sha256_finalize_scratch}
	lea r11, {vg_dsa_probable_prime}
	call {vg_dsa_parameter_search_2048}
	lea rsp, [rsp+56]
	jmp 23b
20:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_sha1_update_scratch}
	lea r10, {vg_sha1_finalize_scratch}
	lea r11, {vg_dsa_probable_prime}
	call {vg_dsa_parameter_search_1024}
	lea rsp, [rsp+56]
	jmp 21b
	.p2align 6
