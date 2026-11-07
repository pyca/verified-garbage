// The functions of `src/internal/vg_chacha20_poly1305_open_body.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_open_body:
	lea rsp, [rsp-1728]
	mov rax, QWORD PTR [rsp+1736]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r11, r8
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
	cmp r13, 1
	jb 20f
	jmp 21f
20:
	mov rdx, r13
21:
	add rdx, 64
	pxor xmm0, xmm0
	mov ecx, 0
22:
	movdqu XMMWORD PTR [r15+rcx*1+672], xmm0
	add rcx, 16
	cmp rcx, rdx
	jb 22b
	mov rdi, r15
	add rdi, 608
	mov rsi, r15
	add rsi, 672
	mov rcx, r15
	add rcx, 128
	mov r8, rsi
	call {vg_chacha20_xor}
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
	je 23f
	call {vg_poly1305_blocks}
	mov r15, rdi
	sub r15, 448
	jmp 24f
23:
24:
	mov rdx, rbp
	and rdx, 15
	je 25f
	mov rsi, rbp
	sub rsi, rdx
	add rsi, rbx
	mov eax, 0
	mov QWORD PTR [r15+576], rax
	mov QWORD PTR [r15+584], rax
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rsi+rcx*1]
	mov BYTE PTR [r15+rcx*1+576], al
	add rcx, 1
	cmp rcx, rdx
	jne 27b
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 576
	mov edx, 1
	call {vg_poly1305_blocks}
	mov r15, rdi
	sub r15, 448
	jmp 26f
25:
26:
	mov QWORD PTR [r15+592], rbp
	mov QWORD PTR [r15+600], r13
	mov rdi, r15
	add rdi, 448
	mov rsi, r12
	mov rdx, r13
	shr rdx, 4
	je 28f
	call {vg_poly1305_blocks}
	mov r15, rdi
	sub r15, 448
	jmp 29f
28:
29:
	mov rdx, r13
	and rdx, 15
	jne 210f
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 592
	mov edx, 1
	call {vg_poly1305_blocks}
	mov r15, rdi
	sub r15, 448
211:
	cmp r13, 1
	jb 213f
	mov edx, 0
	cmp r13, 1
	jb 215f
	jmp 216f
215:
	mov rdx, r13
216:
	test rdx, rdx
	je 217f
	mov rsi, r15
	add rsi, 736
	mov r10, r12
	mov ecx, 0
	mov rax, rdx
	shr rax, 4
	je 219f
221:
	movdqu xmm0, XMMWORD PTR [r10+rcx*1]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r14+rcx*1], xmm0
	add rcx, 16
	sub rax, 1
	jne 221b
	jmp 220f
219:
220:
	mov rdi, r14
	add rdi, rcx
	add r10, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 222f
224:
	mov r8, QWORD PTR [r10+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 224b
	jmp 223f
222:
223:
	cmp rcx, rdx
	je 225f
227:
	movzx eax, BYTE PTR [r10+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 227b
	jmp 226f
225:
226:
	jmp 218f
217:
218:
	mov edx, 0
	cmp r13, 1
	jb 228f
	jmp 229f
228:
	mov rdx, r13
229:
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
	call {vg_chacha20_xor}
	jmp 214f
213:
	mov rsi, r15
	add rsi, 736
	mov rdx, r13
	mov r10, r12
	mov ecx, 0
	mov rax, rdx
	shr rax, 4
	je 230f
232:
	movdqu xmm0, XMMWORD PTR [r10+rcx*1]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r14+rcx*1], xmm0
	add rcx, 16
	sub rax, 1
	jne 232b
	jmp 231f
230:
231:
	mov rdi, r14
	add rdi, rcx
	add r10, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 233f
235:
	mov r8, QWORD PTR [r10+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 235b
	jmp 234f
233:
234:
	cmp rcx, rdx
	je 236f
238:
	movzx eax, BYTE PTR [r10+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 238b
	jmp 237f
236:
237:
	mov rsi, r15
	add rsi, 128
214:
	mov r15, rsi
	sub r15, 128
	mov edx, 0
	cmp r13, 1
	jb 239f
	jmp 240f
239:
	mov rdx, r13
240:
	add rdx, 64
	pxor xmm0, xmm0
	mov ecx, 0
241:
	movdqu XMMWORD PTR [r15+rcx*1+672], xmm0
	add rcx, 16
	cmp rcx, rdx
	jb 241b
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
	je 242f
	jmp 243f
242:
	mov rdx, r14
	mov rcx, r13
	cmp rcx, 0
	je 244f
246:
	mov BYTE PTR [rdx], al
	add rdx, 1
	sub rcx, 1
	jne 246b
	jmp 245f
244:
245:
243:
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
	ret
210:
	mov rsi, r13
	sub rsi, rdx
	add rsi, r12
	mov eax, 0
	mov QWORD PTR [r15+576], rax
	mov QWORD PTR [r15+584], rax
	mov ecx, 0
212:
	movzx eax, BYTE PTR [rsi+rcx*1]
	mov BYTE PTR [r15+rcx*1+576], al
	add rcx, 1
	cmp rcx, rdx
	jne 212b
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 576
	mov edx, 2
	call {vg_poly1305_blocks}
	mov r15, rdi
	sub r15, 448
	jmp 211b
	.p2align 6
