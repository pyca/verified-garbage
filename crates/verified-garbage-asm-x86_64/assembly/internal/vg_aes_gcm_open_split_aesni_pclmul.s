// The functions of `src/internal/vg_aes_gcm_open_split_aesni_pclmul.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_open_split_aesni_pclmul:
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+192], rax
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	cmp rbp, 12
	je 26f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 28f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 29f
28:
29:
	mov rcx, rbp
	test rcx, rcx
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 211f
210:
211:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 27f
26:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
27:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 213f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 214f
213:
214:
	mov rcx, rbp
	test rcx, rcx
	je 215f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+192]
	shr rax, 4
	test rax, rax
	je 218f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+224]
	mov r9, rax
	mov r10, rax
	mov r11, QWORD PTR [r15+200]
	mov rax, r15
	add rax, 448
	push rax
	push r10
	push r11
	call {vg_aes_gcm_decrypt_blocks_to_aesni_pclmul}
	pop rax
	pop rax
	pop rax
	jmp 219f
218:
219:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov QWORD PTR [r15+208], rcx
	add rax, QWORD PTR [r15+224]
	mov QWORD PTR [r15+200], rax
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 220f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 221f
220:
221:
	mov rcx, rbp
	test rcx, rcx
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 223f
222:
223:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 225f
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
226:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 228f
	mov r10d, 0
230:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 230b
	jmp 229f
228:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
229:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 231f
	mov r12, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [r15+192]
	sub rax, QWORD PTR [r15+208]
	add r12, rax
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+200]
	test rbp, rbp
	je 233f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
235:
	movzx eax, BYTE PTR [rbx+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 235b
	jmp 234f
233:
234:
	jmp 232f
231:
232:
	mov rax, QWORD PTR [r15+216]
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	ret
	.p2align 6
