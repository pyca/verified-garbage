// The functions of `src/internal/vg_aes_gcm_stream_encrypt_aesni_pclmul_avx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_stream_encrypt_aesni_pclmul_avx:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
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
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 218f
	jmp 219f
218:
	mov rcx, rbp
219:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 221f
	jmp 222f
221:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
222:
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	jmp 228f
227:
228:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 232f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 233f
232:
233:
	test rbp, rbp
	je 234f
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
236:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	jmp 235f
234:
235:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 237f
	test rbx, rbx
	je 239f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 241f
	jmp 242f
241:
	mov rcx, rbp
242:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 244f
	jmp 245f
244:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
245:
	jmp 240f
239:
240:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 246f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 247f
246:
247:
	mov rcx, rbp
	test rcx, rcx
	je 248f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 238f
237:
238:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6
