// The functions of `src/chacha20.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_init:
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rsi+8]
	mov r8, QWORD PTR [rsi+16]
	mov r9, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rcx
	mov QWORD PTR [rdi+32], r8
	mov QWORD PTR [rdi+40], r9
	mov rsi, rdx
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rsi+8]
	mov edx, DWORD PTR [rsi]
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rcx
	movabs rax, 3684054920433006693
	mov QWORD PTR [rdi], rax
	movabs rax, 7719281312240119090
	mov QWORD PTR [rdi+8], rax
	movabs rcx, 4294967296
	sub rcx, rdx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+128], rcx
	ret
	.p2align 6

vg_chacha20_set_nonce:
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rsi+8]
	mov edx, DWORD PTR [rsi]
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rcx
	movabs rax, 3684054920433006693
	mov QWORD PTR [rdi], rax
	movabs rax, 7719281312240119090
	mov QWORD PTR [rdi+8], rax
	movabs rcx, 4294967296
	sub rcx, rdx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+128], rcx
	ret
	.p2align 6

vg_chacha20_apply_scrub:
	mov rax, QWORD PTR [rdi+128]
	cmp rax, rdx
	jb 20f
	mov QWORD PTR [rdi+576], r13
	mov QWORD PTR [rdi+584], r14
	mov QWORD PTR [rdi+592], r15
	mov r13, rdi
	mov r14, rsi
	mov r15, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [r13+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, r13
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add r14, rdx
	sub r15, rdx
	mov rdx, r15
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [r13]
	mov rcx, QWORD PTR [r13+8]
	mov rsi, QWORD PTR [r13+16]
	mov rdi, QWORD PTR [r13+24]
	mov r8, QWORD PTR [r13+32]
	mov r9, QWORD PTR [r13+40]
	mov r10, QWORD PTR [r13+48]
	mov r11, QWORD PTR [r13+56]
	mov QWORD PTR [r13+192], rax
	mov QWORD PTR [r13+200], rcx
	mov QWORD PTR [r13+208], rsi
	mov QWORD PTR [r13+216], rdi
	mov QWORD PTR [r13+224], r8
	mov QWORD PTR [r13+232], r9
	mov QWORD PTR [r13+240], r10
	mov QWORD PTR [r13+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [r13+48], eax
	mov rdi, r13
	add rdi, 192
	mov rsi, r14
	mov rcx, r13
	add rcx, 256
	add r14, rdx
	sub r15, rdx
	call {vg_chacha20_xor}
	jmp 211f
210:
211:
	test r15, r15
	je 212f
	mov rdi, r13
	mov rsi, r13
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [r13+48]
	add eax, 1
	mov DWORD PTR [r13+48], eax
	mov rsi, r13
	add rsi, 64
	mov rdx, r15
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add r14, rdx
	sub r15, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [r13+600]
	mov QWORD PTR [r13+128], rax
	mov r14, QWORD PTR [r13+584]
	mov r15, QWORD PTR [r13+592]
	mov r13, QWORD PTR [r13+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	lea rsp, [rsp-24]
	lea rsp, [rsp+24]
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

vg_chacha20_apply_avx2_scrub:
	mov rax, QWORD PTR [rdi+128]
	cmp rax, rdx
	jb 20f
	mov QWORD PTR [rdi+576], r13
	mov QWORD PTR [rdi+584], r14
	mov QWORD PTR [rdi+592], r15
	mov r13, rdi
	mov r14, rsi
	mov r15, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [r13+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, r13
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add r14, rdx
	sub r15, rdx
	mov rdx, r15
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [r13]
	mov rcx, QWORD PTR [r13+8]
	mov rsi, QWORD PTR [r13+16]
	mov rdi, QWORD PTR [r13+24]
	mov r8, QWORD PTR [r13+32]
	mov r9, QWORD PTR [r13+40]
	mov r10, QWORD PTR [r13+48]
	mov r11, QWORD PTR [r13+56]
	mov QWORD PTR [r13+192], rax
	mov QWORD PTR [r13+200], rcx
	mov QWORD PTR [r13+208], rsi
	mov QWORD PTR [r13+216], rdi
	mov QWORD PTR [r13+224], r8
	mov QWORD PTR [r13+232], r9
	mov QWORD PTR [r13+240], r10
	mov QWORD PTR [r13+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [r13+48], eax
	mov rdi, r13
	add rdi, 192
	mov rsi, r14
	mov rcx, r13
	add rcx, 256
	add r14, rdx
	sub r15, rdx
	call {vg_chacha20_xor_avx2}
	jmp 211f
210:
211:
	test r15, r15
	je 212f
	mov rdi, r13
	mov rsi, r13
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [r13+48]
	add eax, 1
	mov DWORD PTR [r13+48], eax
	mov rsi, r13
	add rsi, 64
	mov rdx, r15
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add r14, rdx
	sub r15, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [r13+600]
	mov QWORD PTR [r13+128], rax
	mov r14, QWORD PTR [r13+584]
	mov r15, QWORD PTR [r13+592]
	mov r13, QWORD PTR [r13+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
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
	lea rsp, [rsp-24]
	lea rsp, [rsp+24]
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

vg_chacha20_apply_avx512_scrub:
	mov rax, QWORD PTR [rdi+128]
	cmp rax, rdx
	jb 20f
	mov QWORD PTR [rdi+576], r13
	mov QWORD PTR [rdi+584], r14
	mov QWORD PTR [rdi+592], r15
	mov r13, rdi
	mov r14, rsi
	mov r15, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [r13+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, r13
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add r14, rdx
	sub r15, rdx
	mov rdx, r15
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [r13]
	mov rcx, QWORD PTR [r13+8]
	mov rsi, QWORD PTR [r13+16]
	mov rdi, QWORD PTR [r13+24]
	mov r8, QWORD PTR [r13+32]
	mov r9, QWORD PTR [r13+40]
	mov r10, QWORD PTR [r13+48]
	mov r11, QWORD PTR [r13+56]
	mov QWORD PTR [r13+192], rax
	mov QWORD PTR [r13+200], rcx
	mov QWORD PTR [r13+208], rsi
	mov QWORD PTR [r13+216], rdi
	mov QWORD PTR [r13+224], r8
	mov QWORD PTR [r13+232], r9
	mov QWORD PTR [r13+240], r10
	mov QWORD PTR [r13+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [r13+48], eax
	mov rdi, r13
	add rdi, 192
	mov rsi, r14
	mov rcx, r13
	add rcx, 256
	add r14, rdx
	sub r15, rdx
	call {vg_chacha20_xor_avx512}
	jmp 211f
210:
211:
	test r15, r15
	je 212f
	mov rdi, r13
	mov rsi, r13
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [r13+48]
	add eax, 1
	mov DWORD PTR [r13+48], eax
	mov rsi, r13
	add rsi, 64
	mov rdx, r15
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add r14, rdx
	sub r15, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [r13+600]
	mov QWORD PTR [r13+128], rax
	mov r14, QWORD PTR [r13+584]
	mov r15, QWORD PTR [r13+592]
	mov r13, QWORD PTR [r13+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
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
	lea rsp, [rsp-24]
	lea rsp, [rsp+24]
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

vg_chacha20_apply_avx2:
	mov rax, QWORD PTR [rdi+128]
	cmp rax, rdx
	jb 20f
	mov QWORD PTR [rdi+576], r13
	mov QWORD PTR [rdi+584], r14
	mov QWORD PTR [rdi+592], r15
	mov r13, rdi
	mov r14, rsi
	mov r15, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [r13+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, r13
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add r14, rdx
	sub r15, rdx
	mov rdx, r15
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [r13]
	mov rcx, QWORD PTR [r13+8]
	mov rsi, QWORD PTR [r13+16]
	mov rdi, QWORD PTR [r13+24]
	mov r8, QWORD PTR [r13+32]
	mov r9, QWORD PTR [r13+40]
	mov r10, QWORD PTR [r13+48]
	mov r11, QWORD PTR [r13+56]
	mov QWORD PTR [r13+192], rax
	mov QWORD PTR [r13+200], rcx
	mov QWORD PTR [r13+208], rsi
	mov QWORD PTR [r13+216], rdi
	mov QWORD PTR [r13+224], r8
	mov QWORD PTR [r13+232], r9
	mov QWORD PTR [r13+240], r10
	mov QWORD PTR [r13+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [r13+48], eax
	mov rdi, r13
	add rdi, 192
	mov rsi, r14
	mov rcx, r13
	add rcx, 256
	add r14, rdx
	sub r15, rdx
	call {vg_chacha20_xor_avx2}
	jmp 211f
210:
211:
	test r15, r15
	je 212f
	mov rdi, r13
	mov rsi, r13
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [r13+48]
	add eax, 1
	mov DWORD PTR [r13+48], eax
	mov rsi, r13
	add rsi, 64
	mov rdx, r15
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add r14, rdx
	sub r15, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [r13+600]
	mov QWORD PTR [r13+128], rax
	mov r14, QWORD PTR [r13+584]
	mov r15, QWORD PTR [r13+592]
	mov r13, QWORD PTR [r13+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6

// vg_chacha20_apply_avx512: the function `vg_chacha20_apply_ifma`

vg_chacha20_apply_avx512vl:
	mov rax, QWORD PTR [rdi+128]
	cmp rax, rdx
	jb 20f
	mov QWORD PTR [rdi+576], r13
	mov QWORD PTR [rdi+584], r14
	mov QWORD PTR [rdi+592], r15
	mov r13, rdi
	mov r14, rsi
	mov r15, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [r13+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, r13
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add r14, rdx
	sub r15, rdx
	mov rdx, r15
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [r13]
	mov rcx, QWORD PTR [r13+8]
	mov rsi, QWORD PTR [r13+16]
	mov rdi, QWORD PTR [r13+24]
	mov r8, QWORD PTR [r13+32]
	mov r9, QWORD PTR [r13+40]
	mov r10, QWORD PTR [r13+48]
	mov r11, QWORD PTR [r13+56]
	mov QWORD PTR [r13+192], rax
	mov QWORD PTR [r13+200], rcx
	mov QWORD PTR [r13+208], rsi
	mov QWORD PTR [r13+216], rdi
	mov QWORD PTR [r13+224], r8
	mov QWORD PTR [r13+232], r9
	mov QWORD PTR [r13+240], r10
	mov QWORD PTR [r13+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [r13+48], eax
	mov rdi, r13
	add rdi, 192
	mov rsi, r14
	mov rcx, r13
	add rcx, 256
	add r14, rdx
	sub r15, rdx
	call {vg_chacha20_xor_avx512vl}
	jmp 211f
210:
211:
	test r15, r15
	je 212f
	mov rdi, r13
	mov rsi, r13
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [r13+48]
	add eax, 1
	mov DWORD PTR [r13+48], eax
	mov rsi, r13
	add rsi, 64
	mov rdx, r15
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add r14, rdx
	sub r15, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [r13+600]
	mov QWORD PTR [r13+128], rax
	mov r14, QWORD PTR [r13+584]
	mov r15, QWORD PTR [r13+592]
	mov r13, QWORD PTR [r13+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6

vg_chacha20_apply_ifma:
	mov rax, QWORD PTR [rdi+128]
	cmp rax, rdx
	jb 20f
	mov QWORD PTR [rdi+576], r13
	mov QWORD PTR [rdi+584], r14
	mov QWORD PTR [rdi+592], r15
	mov r13, rdi
	mov r14, rsi
	mov r15, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [r13+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, r13
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add r14, rdx
	sub r15, rdx
	mov rdx, r15
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [r13]
	mov rcx, QWORD PTR [r13+8]
	mov rsi, QWORD PTR [r13+16]
	mov rdi, QWORD PTR [r13+24]
	mov r8, QWORD PTR [r13+32]
	mov r9, QWORD PTR [r13+40]
	mov r10, QWORD PTR [r13+48]
	mov r11, QWORD PTR [r13+56]
	mov QWORD PTR [r13+192], rax
	mov QWORD PTR [r13+200], rcx
	mov QWORD PTR [r13+208], rsi
	mov QWORD PTR [r13+216], rdi
	mov QWORD PTR [r13+224], r8
	mov QWORD PTR [r13+232], r9
	mov QWORD PTR [r13+240], r10
	mov QWORD PTR [r13+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [r13+48], eax
	mov rdi, r13
	add rdi, 192
	mov rsi, r14
	mov rcx, r13
	add rcx, 256
	add r14, rdx
	sub r15, rdx
	call {vg_chacha20_xor_avx512}
	jmp 211f
210:
211:
	test r15, r15
	je 212f
	mov rdi, r13
	mov rsi, r13
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [r13+48]
	add eax, 1
	mov DWORD PTR [r13+48], eax
	mov rsi, r13
	add rsi, 64
	mov rdx, r15
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add r14, rdx
	sub r15, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [r13+600]
	mov QWORD PTR [r13+128], rax
	mov r14, QWORD PTR [r13+584]
	mov r15, QWORD PTR [r13+592]
	mov r13, QWORD PTR [r13+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6

vg_chacha20_apply:
	mov rax, QWORD PTR [rdi+128]
	cmp rax, rdx
	jb 20f
	mov QWORD PTR [rdi+576], r13
	mov QWORD PTR [rdi+584], r14
	mov QWORD PTR [rdi+592], r15
	mov r13, rdi
	mov r14, rsi
	mov r15, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [r13+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, r13
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add r14, rdx
	sub r15, rdx
	mov rdx, r15
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [r13]
	mov rcx, QWORD PTR [r13+8]
	mov rsi, QWORD PTR [r13+16]
	mov rdi, QWORD PTR [r13+24]
	mov r8, QWORD PTR [r13+32]
	mov r9, QWORD PTR [r13+40]
	mov r10, QWORD PTR [r13+48]
	mov r11, QWORD PTR [r13+56]
	mov QWORD PTR [r13+192], rax
	mov QWORD PTR [r13+200], rcx
	mov QWORD PTR [r13+208], rsi
	mov QWORD PTR [r13+216], rdi
	mov QWORD PTR [r13+224], r8
	mov QWORD PTR [r13+232], r9
	mov QWORD PTR [r13+240], r10
	mov QWORD PTR [r13+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [r13+48], eax
	mov rdi, r13
	add rdi, 192
	mov rsi, r14
	mov rcx, r13
	add rcx, 256
	add r14, rdx
	sub r15, rdx
	call {vg_chacha20_xor}
	jmp 211f
210:
211:
	test r15, r15
	je 212f
	mov rdi, r13
	mov rsi, r13
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [r13+48]
	add eax, 1
	mov DWORD PTR [r13+48], eax
	mov rsi, r13
	add rsi, 64
	mov rdx, r15
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [r14+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [r14+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [r14+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [r14+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add r14, rdx
	sub r15, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [r13+600]
	mov QWORD PTR [r13+128], rax
	mov r14, QWORD PTR [r13+584]
	mov r15, QWORD PTR [r13+592]
	mov r13, QWORD PTR [r13+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6
