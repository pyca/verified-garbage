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

vg_chacha20_apply_avx2:
	mov rax, QWORD PTR [rdi+128]
	cmp rax, rdx
	jb 20f
	mov QWORD PTR [rdi+576], rbx
	mov QWORD PTR [rdi+584], rbp
	mov QWORD PTR [rdi+592], r12
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [rbx+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, rbx
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [rbp+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rbp+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [rbp+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rbp+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add rbp, rdx
	sub r12, rdx
	mov rdx, r12
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [rbx]
	mov rcx, QWORD PTR [rbx+8]
	mov rsi, QWORD PTR [rbx+16]
	mov rdi, QWORD PTR [rbx+24]
	mov r8, QWORD PTR [rbx+32]
	mov r9, QWORD PTR [rbx+40]
	mov r10, QWORD PTR [rbx+48]
	mov r11, QWORD PTR [rbx+56]
	mov QWORD PTR [rbx+192], rax
	mov QWORD PTR [rbx+200], rcx
	mov QWORD PTR [rbx+208], rsi
	mov QWORD PTR [rbx+216], rdi
	mov QWORD PTR [rbx+224], r8
	mov QWORD PTR [rbx+232], r9
	mov QWORD PTR [rbx+240], r10
	mov QWORD PTR [rbx+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [rbx+48], eax
	mov rdi, rbx
	add rdi, 192
	mov rsi, rbp
	mov rcx, rbx
	add rcx, 256
	add rbp, rdx
	sub r12, rdx
	call {vg_chacha20_xor_avx2}
	jmp 211f
210:
211:
	test r12, r12
	je 212f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [rbx+48]
	add eax, 1
	mov DWORD PTR [rbx+48], eax
	mov rsi, rbx
	add rsi, 64
	mov rdx, r12
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [rbp+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rbp+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [rbp+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rbp+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add rbp, rdx
	sub r12, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbx+128], rax
	mov rbp, QWORD PTR [rbx+584]
	mov r12, QWORD PTR [rbx+592]
	mov rbx, QWORD PTR [rbx+576]
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
	mov QWORD PTR [rdi+576], rbx
	mov QWORD PTR [rdi+584], rbp
	mov QWORD PTR [rdi+592], r12
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [rbx+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, rbx
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [rbp+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rbp+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [rbp+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rbp+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add rbp, rdx
	sub r12, rdx
	mov rdx, r12
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [rbx]
	mov rcx, QWORD PTR [rbx+8]
	mov rsi, QWORD PTR [rbx+16]
	mov rdi, QWORD PTR [rbx+24]
	mov r8, QWORD PTR [rbx+32]
	mov r9, QWORD PTR [rbx+40]
	mov r10, QWORD PTR [rbx+48]
	mov r11, QWORD PTR [rbx+56]
	mov QWORD PTR [rbx+192], rax
	mov QWORD PTR [rbx+200], rcx
	mov QWORD PTR [rbx+208], rsi
	mov QWORD PTR [rbx+216], rdi
	mov QWORD PTR [rbx+224], r8
	mov QWORD PTR [rbx+232], r9
	mov QWORD PTR [rbx+240], r10
	mov QWORD PTR [rbx+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [rbx+48], eax
	mov rdi, rbx
	add rdi, 192
	mov rsi, rbp
	mov rcx, rbx
	add rcx, 256
	add rbp, rdx
	sub r12, rdx
	call {vg_chacha20_xor_avx512vl}
	jmp 211f
210:
211:
	test r12, r12
	je 212f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [rbx+48]
	add eax, 1
	mov DWORD PTR [rbx+48], eax
	mov rsi, rbx
	add rsi, 64
	mov rdx, r12
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [rbp+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rbp+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [rbp+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rbp+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add rbp, rdx
	sub r12, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbx+128], rax
	mov rbp, QWORD PTR [rbx+584]
	mov r12, QWORD PTR [rbx+592]
	mov rbx, QWORD PTR [rbx+576]
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
	mov QWORD PTR [rdi+576], rbx
	mov QWORD PTR [rdi+584], rbp
	mov QWORD PTR [rdi+592], r12
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [rbx+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, rbx
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [rbp+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rbp+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [rbp+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rbp+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add rbp, rdx
	sub r12, rdx
	mov rdx, r12
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [rbx]
	mov rcx, QWORD PTR [rbx+8]
	mov rsi, QWORD PTR [rbx+16]
	mov rdi, QWORD PTR [rbx+24]
	mov r8, QWORD PTR [rbx+32]
	mov r9, QWORD PTR [rbx+40]
	mov r10, QWORD PTR [rbx+48]
	mov r11, QWORD PTR [rbx+56]
	mov QWORD PTR [rbx+192], rax
	mov QWORD PTR [rbx+200], rcx
	mov QWORD PTR [rbx+208], rsi
	mov QWORD PTR [rbx+216], rdi
	mov QWORD PTR [rbx+224], r8
	mov QWORD PTR [rbx+232], r9
	mov QWORD PTR [rbx+240], r10
	mov QWORD PTR [rbx+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [rbx+48], eax
	mov rdi, rbx
	add rdi, 192
	mov rsi, rbp
	mov rcx, rbx
	add rcx, 256
	add rbp, rdx
	sub r12, rdx
	call {vg_chacha20_xor_avx512}
	jmp 211f
210:
211:
	test r12, r12
	je 212f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [rbx+48]
	add eax, 1
	mov DWORD PTR [rbx+48], eax
	mov rsi, rbx
	add rsi, 64
	mov rdx, r12
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [rbp+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rbp+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [rbp+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rbp+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add rbp, rdx
	sub r12, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbx+128], rax
	mov rbp, QWORD PTR [rbx+584]
	mov r12, QWORD PTR [rbx+592]
	mov rbx, QWORD PTR [rbx+576]
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
	mov QWORD PTR [rdi+576], rbx
	mov QWORD PTR [rdi+584], rbp
	mov QWORD PTR [rdi+592], r12
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov rcx, rax
	sub rcx, rdx
	mov QWORD PTR [rbx+600], rcx
	and rax, 63
	cmp rax, rdx
	jb 22f
	jmp 23f
22:
	mov rdx, rax
23:
	mov rsi, rbx
	add rsi, 128
	sub rsi, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 24f
26:
	mov r8, QWORD PTR [rbp+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rbp+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp rcx, rdx
	je 27f
29:
	movzx eax, BYTE PTR [rbp+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rbp+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 29b
	jmp 28f
27:
28:
	add rbp, rdx
	sub r12, rdx
	mov rdx, r12
	and rdx, -64
	je 210f
	mov rax, QWORD PTR [rbx]
	mov rcx, QWORD PTR [rbx+8]
	mov rsi, QWORD PTR [rbx+16]
	mov rdi, QWORD PTR [rbx+24]
	mov r8, QWORD PTR [rbx+32]
	mov r9, QWORD PTR [rbx+40]
	mov r10, QWORD PTR [rbx+48]
	mov r11, QWORD PTR [rbx+56]
	mov QWORD PTR [rbx+192], rax
	mov QWORD PTR [rbx+200], rcx
	mov QWORD PTR [rbx+208], rsi
	mov QWORD PTR [rbx+216], rdi
	mov QWORD PTR [rbx+224], r8
	mov QWORD PTR [rbx+232], r9
	mov QWORD PTR [rbx+240], r10
	mov QWORD PTR [rbx+248], r11
	mov eax, r10d
	mov rcx, rdx
	shr rcx, 6
	add eax, ecx
	mov DWORD PTR [rbx+48], eax
	mov rdi, rbx
	add rdi, 192
	mov rsi, rbp
	mov rcx, rbx
	add rcx, 256
	add rbp, rdx
	sub r12, rdx
	call {vg_chacha20_xor}
	jmp 211f
210:
211:
	test r12, r12
	je 212f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	call {vg_chacha20_block}
	mov eax, DWORD PTR [rbx+48]
	add eax, 1
	mov DWORD PTR [rbx+48], eax
	mov rsi, rbx
	add rsi, 64
	mov rdx, r12
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 214f
216:
	mov r8, QWORD PTR [rbp+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rbp+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 216b
	jmp 215f
214:
215:
	cmp rcx, rdx
	je 217f
219:
	movzx eax, BYTE PTR [rbp+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rbp+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 219b
	jmp 218f
217:
218:
	add rbp, rdx
	sub r12, rdx
	jmp 213f
212:
213:
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbx+128], rax
	mov rbp, QWORD PTR [rbx+584]
	mov r12, QWORD PTR [rbx+592]
	mov rbx, QWORD PTR [rbx+576]
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6
