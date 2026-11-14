// The functions of `src/internal/vg_aes_gcm_seal_prepared_vaes_vpclmul_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_prepared_vaes_vpclmul_core:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
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
	cmp rbp, 12
	je 22f
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
	je 24f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 25f
24:
25:
	mov rcx, rbp
	test rcx, rcx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 27f
26:
27:
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
	call {vg_ghash_vpclmul}
	jmp 23f
22:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
23:
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
	je 29f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 210f
29:
210:
	mov rcx, rbp
	test rcx, rcx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 212f
211:
212:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 214f
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
	call {vg_aes_gcm_encrypt_blocks_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 215f
214:
215:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 216f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 217f
216:
217:
	test rbp, rbp
	je 218f
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
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	jmp 219f
218:
219:
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
	je 221f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 222f
221:
222:
	mov rcx, rbp
	test rcx, rcx
	je 223f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 224f
223:
224:
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
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
21:
	ret
20:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
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
	cmp rbp, 12
	je 226f
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
	je 228f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 229f
228:
229:
	mov rcx, rbp
	test rcx, rcx
	je 230f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
232:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 232b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 231f
230:
231:
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
	call {vg_ghash_vpclmul}
	jmp 227f
226:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
227:
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
	je 233f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 234f
233:
234:
	mov rcx, rbp
	test rcx, rcx
	je 235f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 236f
235:
236:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 238f
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
	call {vg_aes_gcm_encrypt_blocks_prepared16_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 239f
238:
239:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 240f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 241f
240:
241:
	test rbp, rbp
	je 242f
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
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
244:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 244b
	jmp 243f
242:
243:
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
	je 245f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 246f
245:
246:
	mov rcx, rbp
	test rcx, rcx
	je 247f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
249:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 249b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 248f
247:
248:
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
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	jmp 21b
	.p2align 6
