// The functions of `src/internal/vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512_core:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 48
	jae 20f
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
	je 22f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 24f
	jmp 25f
24:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
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
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 27f
26:
27:
25:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 29f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 211f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 213f
	jmp 214f
213:
	mov rcx, rbp
214:
	jmp 212f
211:
	mov ecx, 0
212:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 215f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 217f
	jmp 218f
217:
	mov rcx, rbp
218:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 223f
	jmp 224f
223:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
224:
	jmp 216f
215:
216:
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
	je 225f
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
	call {vg_aes_gcm_encrypt_blocks_vaes_vpclmul_avx512}
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
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 210f
29:
210:
	test rbp, rbp
	je 227f
	test rbx, rbx
	je 229f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 231f
	jmp 232f
231:
	mov rcx, rbp
232:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	add r12, rcx
	sub rbp, rcx
	jmp 230f
229:
230:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 234f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 235f
234:
235:
	test rbp, rbp
	je 236f
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
238:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 228f
227:
228:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 246f
	jmp 247f
246:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
247:
	jmp 242f
241:
242:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 248f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 249f
248:
249:
	mov rcx, rbp
	test rcx, rcx
	je 250f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
252:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 252b
	jmp 251f
250:
251:
	jmp 240f
239:
240:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
21:
	ret
20:
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
	je 253f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 255f
	jmp 256f
255:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 257f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
259:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 259b
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
	jmp 258f
257:
258:
256:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 260f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 262f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 264f
	jmp 265f
264:
	mov rcx, rbp
265:
	jmp 263f
262:
	mov ecx, 0
263:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 266f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 268f
	jmp 269f
268:
	mov rcx, rbp
269:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
270:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 270b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 271f
	jmp 272f
271:
	mov rcx, rbp
272:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 274f
	jmp 275f
274:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
275:
	jmp 267f
266:
267:
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
	je 276f
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
	call {vg_aes_gcm_encrypt_blocks_prepared_vaes_vpclmul_avx512}
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
	jmp 277f
276:
277:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 261f
260:
261:
	test rbp, rbp
	je 278f
	test rbx, rbx
	je 280f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 282f
	jmp 283f
282:
	mov rcx, rbp
283:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
284:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 284b
	add r12, rcx
	sub rbp, rcx
	jmp 281f
280:
281:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 285f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 286f
285:
286:
	test rbp, rbp
	je 287f
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
289:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 289b
	jmp 288f
287:
288:
	jmp 279f
278:
279:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 290f
	test rbx, rbx
	je 292f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 294f
	jmp 295f
294:
	mov rcx, rbp
295:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
296:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 296b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 297f
	jmp 298f
297:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
298:
	jmp 293f
292:
293:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 299f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2100f
299:
2100:
	mov rcx, rbp
	test rcx, rcx
	je 2101f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	jmp 2102f
2101:
2102:
	jmp 291f
290:
291:
	jmp 254f
253:
254:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	jmp 21b
	.p2align 6
