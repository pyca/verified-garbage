// The functions of `src/internal/vg_chacha20_poly1305_seal_avx512vl_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_avx512vl_core:
	mov eax, 0
	mov rax, r9
	mov r10, r9
	sub r10, 961
	cmp r10, 64
	mov r10, 0
	cmovb rax, r10
	cmp rax, 768
	jb 20f
	lea rsp, [rsp-1728]
	mov rax, QWORD PTR [rsp+1736]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov r11, QWORD PTR [rsp+8]
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
	jb 22f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 24f
	mov edx, 0
	jmp 25f
24:
25:
	jmp 23f
22:
	mov rdx, r13
23:
	add rdx, 64
	vpxord zmm0, zmm0, zmm0
	mov ecx, 0
26:
	vmovdqu32 ZMMWORD PTR [r15+rcx*1+672], zmm0
	add rcx, 64
	cmp rcx, rdx
	jb 26b
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
	call {vg_poly1305_init_core}
	mov r15, rdi
	sub r15, 448
	mov rdi, r15
	add rdi, 448
	mov rsi, rbx
	mov rdx, rbp
	shr rdx, 4
	je 27f
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 28f
27:
28:
	mov rdx, rbp
	and rdx, 15
	jne 29f
	je 211f
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
	jmp 212f
211:
212:
210:
	mov QWORD PTR [r15+592], rbp
	mov QWORD PTR [r15+600], r13
	cmp r13, 961
	jb 221f
	mov edx, 0
	cmp r13, 961
	jb 223f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 225f
	mov edx, 0
	jmp 226f
225:
226:
	jmp 224f
223:
	mov rdx, r13
224:
	test rdx, rdx
	je 227f
	mov rsi, r15
	add rsi, 736
	mov ecx, 0
	mov rax, rdx
	shr rax, 6
	je 229f
231:
	vmovdqu32 zmm0, ZMMWORD PTR [r14+rcx*1]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [r14+rcx*1], zmm0
	add rcx, 64
	sub rax, 1
	jne 231b
	jmp 230f
229:
230:
	mov rdi, r14
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 232f
234:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 234b
	jmp 233f
232:
233:
	cmp rcx, rdx
	je 235f
237:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 237b
	jmp 236f
235:
236:
	jmp 228f
227:
228:
	mov edx, 0
	cmp r13, 961
	jb 238f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 240f
	mov edx, 0
	jmp 241f
240:
241:
	jmp 239f
238:
	mov rdx, r13
239:
	mov rax, rdx
	shr rax, 6
	add rax, 1
	mov DWORD PTR [r15+112], eax
	mov rsi, r14
	add rsi, rdx
	mov rax, r13
	sub rax, rdx
	mov rdx, rax
	mov rdi, r15
	add rdi, 64
	mov rcx, r15
	add rcx, 128
	mov r8, rsi
	call {vg_chacha20_xor_avx512vl}
	jmp 222f
221:
	mov rsi, r15
	add rsi, 736
	mov rdx, r13
	mov ecx, 0
	mov rax, rdx
	shr rax, 6
	je 242f
244:
	vmovdqu32 zmm0, ZMMWORD PTR [r14+rcx*1]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [r14+rcx*1], zmm0
	add rcx, 64
	sub rax, 1
	jne 244b
	jmp 243f
242:
243:
	mov rdi, r14
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 245f
247:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 247b
	jmp 246f
245:
246:
	cmp rcx, rdx
	je 248f
250:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 250b
	jmp 249f
248:
249:
	mov rsi, r15
	add rsi, 128
222:
	mov r15, rsi
	sub r15, 128
	mov edx, 0
	cmp r13, 961
	jb 251f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 253f
	mov edx, 0
	jmp 254f
253:
254:
	jmp 252f
251:
	mov rdx, r13
252:
	add rdx, 64
	vpxord zmm0, zmm0, zmm0
	mov ecx, 0
255:
	vmovdqu32 ZMMWORD PTR [r15+rcx*1+672], zmm0
	add rcx, 64
	cmp rcx, rdx
	jb 255b
	vzeroupper
	mov rdi, r15
	add rdi, 448
	mov rsi, r14
	mov rdx, r13
	shr rdx, 4
	je 256f
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 257f
256:
257:
	mov rdx, r13
	and rdx, 15
	jne 258f
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 592
	mov edx, 1
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
259:
	mov rdi, r15
	add rdi, 448
	mov esi, 0
	mov rdx, r12
	call {vg_poly1305_finalize_scratch}
	mov r15, rdi
	sub r15, 448
	mov rbx, QWORD PTR [r15]
	mov rbp, QWORD PTR [r15+8]
	mov r13, QWORD PTR [r15+16]
	mov r14, QWORD PTR [r15+24]
	mov r12, QWORD PTR [r15+40]
	mov r15, QWORD PTR [r15+32]
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	lea rsp, [rsp+1728]
21:
	ret
29:
	jne 213f
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	mov eax, 0
	add rax, 1
	jmp 214f
213:
214:
	mov rsi, rbp
	sub rsi, rdx
	add rsi, rbx
	xor r9d, r9d
	cmp rdx, 8
	jb 215f
	mov rax, QWORD PTR [rsi]
	add rsi, 8
	sub rdx, 8
	je 217f
219:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 219b
	jmp 218f
217:
218:
	jmp 216f
215:
220:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 220b
	mov rax, r9
	xor r9d, r9d
216:
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
	jmp 210b
258:
	mov rsi, r13
	sub rsi, rdx
	add rsi, r14
	xor r9d, r9d
	cmp rdx, 8
	jb 260f
	mov rax, QWORD PTR [rsi]
	add rsi, 8
	sub rdx, 8
	je 262f
264:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 264b
	jmp 263f
262:
263:
	jmp 261f
260:
265:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 265b
	mov rax, r9
	xor r9d, r9d
261:
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
	jmp 259b
20:
	lea rsp, [rsp-8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rsp], rax
	call {vg_chacha20_poly1305_seal_body_avx512vl}
	lea rsp, [rsp+8]
	jmp 21b
	.p2align 6
