// The functions of `src/internal/vg_chacha20_poly1305_open_body_avx512vl_large.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_open_body_avx512vl_large:
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax], rbx
	mov QWORD PTR [rax+8], rbp
	mov QWORD PTR [rax+16], r13
	mov QWORD PTR [rax+24], r14
	mov QWORD PTR [rax+32], r15
	mov QWORD PTR [rax+40], r12
	mov r15, rax
	mov r12, r11
	mov rbx, rdx
	mov rbp, rcx
	mov r14, r8
	mov r13, r9
	movabs rax, 3684054920433006693
	mov QWORD PTR [r15+64], rax
	movabs rax, 7719281312240119090
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r15+80], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r15+104], rax
	mov eax, DWORD PTR [rsi]
	shl rax, 32
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [rsi+4]
	mov QWORD PTR [r15+120], rax
	movabs rax, 3684054920433006693
	mov QWORD PTR [r15+608], rax
	movabs rax, 7719281312240119090
	mov QWORD PTR [r15+616], rax
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r15+624], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r15+632], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r15+640], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r15+648], rax
	mov eax, DWORD PTR [rsi]
	shl rax, 32
	mov QWORD PTR [r15+656], rax
	mov rax, QWORD PTR [rsi+4]
	mov QWORD PTR [r15+664], rax
	mov edx, 0
	cmp r13, 961
	jb 20f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 22f
	mov edx, 0
	jmp 23f
22:
23:
	jmp 21f
20:
	mov rdx, r13
21:
	add rdx, 64
	vpxord zmm0, zmm0, zmm0
	mov ecx, 0
24:
	vmovdqu32 ZMMWORD PTR [r15+rcx*1+672], zmm0
	add rcx, 64
	cmp rcx, rdx
	jb 24b
	vzeroupper
	mov rdi, r15
	add rdi, 608
	mov rsi, r15
	add rsi, 672
	mov rcx, r15
	add rcx, 128
	mov r8, rsi
	call {vg_chacha20_xor_avx512vl}
	mov r15, rsi
	sub r15, 128
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 672
	call {vg_poly1305_init}
	mov r15, rdi
	sub r15, 448
	mov rdi, r15
	add rdi, 448
	mov rsi, rbx
	mov rdx, rbp
	shr rdx, 4
	je 25f
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 26f
25:
26:
	mov rdx, rbp
	and rdx, 15
	jne 27f
	je 29f
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	add rax, 1
	add rax, 1
	jmp 210f
29:
210:
28:
	mov QWORD PTR [r15+592], rbp
	mov QWORD PTR [r15+600], r13
	mov rdi, r15
	add rdi, 448
	mov rsi, r12
	mov rdx, r13
	shr rdx, 4
	je 219f
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 220f
219:
220:
	mov rdx, r13
	and rdx, 15
	jne 221f
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 592
	mov edx, 1
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
222:
	cmp r13, 961
	jb 229f
	mov edx, 0
	cmp r13, 961
	jb 231f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 233f
	mov edx, 0
	jmp 234f
233:
234:
	jmp 232f
231:
	mov rdx, r13
232:
	test rdx, rdx
	je 235f
	mov rsi, r15
	add rsi, 736
	mov r10, r12
	mov ecx, 0
	mov rax, rdx
	shr rax, 6
	je 237f
239:
	vmovdqu32 zmm0, ZMMWORD PTR [r10+rcx*1]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [r14+rcx*1], zmm0
	add rcx, 64
	sub rax, 1
	jne 239b
	jmp 238f
237:
238:
	mov rdi, r14
	add rdi, rcx
	add r10, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 240f
242:
	mov r8, QWORD PTR [r10+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 242b
	jmp 241f
240:
241:
	cmp rcx, rdx
	je 243f
245:
	movzx eax, BYTE PTR [r10+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 245b
	jmp 244f
243:
244:
	jmp 236f
235:
236:
	mov edx, 0
	cmp r13, 961
	jb 246f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 248f
	mov edx, 0
	jmp 249f
248:
249:
	jmp 247f
246:
	mov rdx, r13
247:
	mov rax, rdx
	shr rax, 6
	add rax, 1
	mov DWORD PTR [r15+112], eax
	mov rsi, r12
	add rsi, rdx
	mov rax, r13
	sub rax, rdx
	mov rdx, rax
	mov rdi, r15
	add rdi, 64
	mov rcx, r15
	add rcx, 128
	mov r11, r14
	sub r11, r12
	mov r8, r11
	add r8, rsi
	call {vg_chacha20_xor_avx512vl}
	jmp 230f
229:
	mov rsi, r15
	add rsi, 736
	mov rdx, r13
	mov r10, r12
	mov ecx, 0
	mov rax, rdx
	shr rax, 6
	je 250f
252:
	vmovdqu32 zmm0, ZMMWORD PTR [r10+rcx*1]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [r14+rcx*1], zmm0
	add rcx, 64
	sub rax, 1
	jne 252b
	jmp 251f
250:
251:
	mov rdi, r14
	add rdi, rcx
	add r10, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 253f
255:
	mov r8, QWORD PTR [r10+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 255b
	jmp 254f
253:
254:
	cmp rcx, rdx
	je 256f
258:
	movzx eax, BYTE PTR [r10+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 258b
	jmp 257f
256:
257:
	mov rsi, r15
	add rsi, 128
230:
	mov r15, rsi
	sub r15, 128
	mov edx, 0
	cmp r13, 961
	jb 259f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 261f
	mov edx, 0
	jmp 262f
261:
262:
	jmp 260f
259:
	mov rdx, r13
260:
	add rdx, 64
	vpxord zmm0, zmm0, zmm0
	mov ecx, 0
263:
	vmovdqu32 ZMMWORD PTR [r15+rcx*1+672], zmm0
	add rcx, 64
	cmp rcx, rdx
	jb 263b
	vzeroupper
	mov rdi, r15
	add rdi, 448
	mov esi, 0
	mov rdx, r15
	add rdx, 48
	call {vg_poly1305_finalize_scratch}
	mov r12, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rcx]
	xor rax, QWORD PTR [r12]
	mov rdx, QWORD PTR [rcx+8]
	xor rdx, QWORD PTR [r12+8]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	cmp eax, 0
	je 264f
	jmp 265f
264:
	mov rdx, r14
	mov rcx, r13
	cmp rcx, 0
	je 266f
268:
	mov BYTE PTR [rdx], al
	add rdx, 1
	sub rcx, 1
	jne 268b
	jmp 267f
266:
267:
265:
	mov r15, rdi
	sub r15, 448
	mov rbx, QWORD PTR [r15]
	mov rbp, QWORD PTR [r15+8]
	mov r13, QWORD PTR [r15+16]
	mov r14, QWORD PTR [r15+24]
	mov r12, QWORD PTR [r15+40]
	mov r15, QWORD PTR [r15+32]
	ret
27:
	jne 211f
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	mov eax, 0
	add rax, 1
	jmp 212f
211:
212:
	mov rsi, rbp
	sub rsi, rdx
	add rsi, rbx
	xor r9d, r9d
	cmp rdx, 8
	jb 213f
	mov rax, QWORD PTR [rsi]
	add rsi, 8
	sub rdx, 8
	je 215f
217:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 217b
	jmp 216f
215:
216:
	jmp 214f
213:
218:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 218b
	mov rax, r9
	xor r9d, r9d
214:
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 576
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], r9
	mov edx, 1
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 28b
221:
	mov rsi, r13
	sub rsi, rdx
	add rsi, r12
	xor r9d, r9d
	cmp rdx, 8
	jb 223f
	mov rax, QWORD PTR [rsi]
	add rsi, 8
	sub rdx, 8
	je 225f
227:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 227b
	jmp 226f
225:
226:
	jmp 224f
223:
228:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 228b
	mov rax, r9
	xor r9d, r9d
224:
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 576
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], r9
	mov edx, 2
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 222b
	.p2align 6
