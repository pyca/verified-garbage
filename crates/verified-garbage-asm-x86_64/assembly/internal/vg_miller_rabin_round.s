// The functions of `src/internal/vg_miller_rabin_round.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_miller_rabin_round:
	mov rsi, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov r8, QWORD PTR [rdi+184]
	mov r9, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+152]
	mov r10, QWORD PTR [rdi+160]
	mov r11, QWORD PTR [rdi+200]
	push rbx
	push r12
	push r13
	push r14
	push r15
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push r10
	push r11
	push rbp
	mov rax, QWORD PTR [rdi+48]
	shl rax, 3
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+200], rax
	mov eax, 0
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r9, QWORD PTR [rdi+120]
	add r9, rax
	add r9, rax
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r11, QWORD PTR [rdi+120]
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	add r11, rax
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r13, QWORD PTR [rdi+120]
	add r13, rax
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rcx, QWORD PTR [rdi+120]
	add rcx, rax
	add rcx, rax
	add rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov eax, 14
	mov QWORD PTR [rdi+224], rax
	mov rsi, r8
	mov rbx, r9
	mov r14, 0
20:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 20b
	mov rsi, r8
	mov rbx, r10
	mov r14, 0
21:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 21b
	mov rsi, r11
	mov rbx, r13
	mov r14, 0
22:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 22b
23:
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 24f
	mov eax, 0
	mov r14, 0
26:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 26b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
27:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
28:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 28b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
29:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 29b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 27b
	mov ebp, 0
	mov r14, 0
210:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 210b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
211:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 211b
	jmp 25f
24:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
212:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 212b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
213:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
214:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 214b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 213b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
215:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 215b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
216:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
217:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 217b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 216b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
218:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 218b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
219:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 219b
25:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
220:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 220b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+224]
	sub rax, 1
	mov QWORD PTR [rdi+224], rax
	jne 23b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+120]
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	add rsi, rax
	mov r14, 0
221:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 221b
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+216], rax
	mov eax, 0
	mov QWORD PTR [rdi+176], rax
222:
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, QWORD PTR [rdi+120]
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	add rdx, rax
	mov rax, QWORD PTR [rdi+216]
	mov rcx, QWORD PTR [rdx+rax*8]
	mov QWORD PTR [rdi+208], rcx
	mov ecx, 16
	mov QWORD PTR [rdi+224], rcx
223:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 224f
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
227:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
228:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 228b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
229:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 229b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 227b
	mov ebp, 0
	mov r14, 0
230:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 230b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
231:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 231b
	jmp 225f
224:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 232b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
233:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
234:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 234b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 233b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
235:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 235b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
236:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
237:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 237b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 236b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
238:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 238b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
239:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 239b
225:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r10, QWORD PTR [rdi+120]
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	mov ebp, 0
	mov r14, 0
240:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 240b
	cmp rbp, 1
	sbb rbp, rbp
	mov rax, QWORD PTR [rdi+176]
	or rax, rbp
	mov QWORD PTR [rdi+176], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 241f
	mov eax, 0
	mov r14, 0
243:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 243b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
244:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
245:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 245b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
246:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 246b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 244b
	mov ebp, 0
	mov r14, 0
247:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 247b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
248:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 248b
	jmp 242f
241:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
249:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 249b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
250:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
251:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 251b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 250b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
252:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 252b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
253:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
254:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 254b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 253b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
255:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 255b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
256:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 256b
242:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r10, QWORD PTR [rdi+120]
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	mov ebp, 0
	mov r14, 0
257:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 257b
	cmp rbp, 1
	sbb rbp, rbp
	mov rax, QWORD PTR [rdi+176]
	or rax, rbp
	mov QWORD PTR [rdi+176], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 258f
	mov eax, 0
	mov r14, 0
260:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
261:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
262:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 262b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
263:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 263b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 261b
	mov ebp, 0
	mov r14, 0
264:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 264b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
265:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 265b
	jmp 259f
258:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
266:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 266b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
267:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
268:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 268b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 267b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
269:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 269b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
270:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
271:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 271b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 270b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
272:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 272b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
273:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
259:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r10, QWORD PTR [rdi+120]
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	mov ebp, 0
	mov r14, 0
274:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 274b
	cmp rbp, 1
	sbb rbp, rbp
	mov rax, QWORD PTR [rdi+176]
	or rax, rbp
	mov QWORD PTR [rdi+176], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 275f
	mov eax, 0
	mov r14, 0
277:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
278:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
279:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 279b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
280:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 280b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 278b
	mov ebp, 0
	mov r14, 0
281:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 281b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
282:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 282b
	jmp 276f
275:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
283:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 283b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
284:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
285:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 285b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 284b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
286:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 286b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
287:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
288:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 288b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 287b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
289:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 289b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
290:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 290b
276:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r10, QWORD PTR [rdi+120]
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	mov ebp, 0
	mov r14, 0
291:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 291b
	cmp rbp, 1
	sbb rbp, rbp
	mov rax, QWORD PTR [rdi+176]
	or rax, rbp
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+208]
	shr rax, 60
	mov QWORD PTR [rdi+248], rax
	mov r15d, 0
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rcx, QWORD PTR [rdi+120]
	add rcx, rax
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
292:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 292b
	mov r15d, 8
	mov rax, r11
	add rax, rax
	add rax, rax
	add rax, rax
	add rcx, rax
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+248]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
293:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 293b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 294f
	mov eax, 0
	mov r14, 0
296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
297:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
298:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 298b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
299:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 299b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 297b
	mov ebp, 0
	mov r14, 0
2100:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2101:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2101b
	jmp 295f
294:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2102:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2102b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2103:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2104:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2104b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2103b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2105:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2105b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2106:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2107:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2107b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2106b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2108:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2108b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2109:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2109b
295:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r10, QWORD PTR [rdi+120]
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	mov ebp, 0
	mov r14, 0
2110:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2110b
	cmp rbp, 1
	sbb rbp, rbp
	mov QWORD PTR [rdi+248], rbp
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r10, QWORD PTR [rdi+120]
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	mov ebp, 0
	mov r14, 0
2111:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2111b
	cmp rbp, 1
	sbb rbp, rbp
	mov rax, QWORD PTR [rdi+208]
	shr rax, 60
	cmp rax, 1
	sbb r15, r15
	mov rdx, QWORD PTR [rdi+248]
	or rbp, rdx
	mov rax, QWORD PTR [rdi+176]
	and rax, r15
	xor r15, -1
	and rbp, r15
	or rax, rbp
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+208]
	shl rax, 4
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+224]
	sub rax, 1
	mov QWORD PTR [rdi+224], rax
	jne 223b
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	jne 222b
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2112f
	mov eax, 0
	mov r14, 0
2114:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2115:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2116:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2116b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2117:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2117b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2115b
	mov ebp, 0
	mov r14, 0
2118:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2118b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2119:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	jmp 2113f
2112:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2120:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2120b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2121:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2122:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2122b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2121b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2123:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2123b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2124:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2125:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2125b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2124b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2126:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2127:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2127b
2113:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r10, QWORD PTR [rdi+120]
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	mov ebp, 0
	mov r14, 0
2128:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2128b
	cmp rbp, 1
	sbb rbp, rbp
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rbx, QWORD PTR [rdi+120]
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	mov r12, QWORD PTR [rdi+48]
	movabs rdx, -2459565876494606883
	and rdx, QWORD PTR [rbx+r12*8]
	cmp rdx, 1
	sbb rdx, rdx
	xor rdx, -1
	and rbp, rdx
	mov rax, QWORD PTR [rdi+176]
	or rax, rbp
	mov QWORD PTR [rdi+176], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2129f
	mov eax, 0
	mov r14, 0
2131:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2131b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2132:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2133:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2134:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2132b
	mov ebp, 0
	mov r14, 0
2135:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2135b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2136:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2136b
	jmp 2130f
2129:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2137:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2137b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2138:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2139:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2139b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2138b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2140:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2140b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2141:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2142:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2142b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2141b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2143:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2143b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2144:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
2130:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r10, QWORD PTR [rdi+120]
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	mov ebp, 0
	mov r14, 0
2145:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2145b
	cmp rbp, 1
	sbb rbp, rbp
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rbx, QWORD PTR [rdi+120]
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	mov r12, QWORD PTR [rdi+48]
	movabs rdx, -7378697629483820647
	and rdx, QWORD PTR [rbx+r12*8]
	cmp rdx, 1
	sbb rdx, rdx
	xor rdx, -1
	and rbp, rdx
	mov rax, QWORD PTR [rdi+176]
	or rax, rbp
	mov QWORD PTR [rdi+176], rax
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2146f
	mov eax, 0
	mov r14, 0
2148:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2149:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2150:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2151:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2151b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2149b
	mov ebp, 0
	mov r14, 0
2152:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2153:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2153b
	jmp 2147f
2146:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2154:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2154b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2155:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2156:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2156b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2155b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2157:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2157b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2158:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2159:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2159b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2158b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2160:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2160b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2161:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2161b
2147:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov r10, QWORD PTR [rdi+120]
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	add r10, rax
	mov ebp, 0
	mov r14, 0
2162:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2162b
	cmp rbp, 1
	sbb rbp, rbp
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rbx, QWORD PTR [rdi+120]
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	mov r12, QWORD PTR [rdi+48]
	movabs rdx, 1229782938247303441
	and rdx, QWORD PTR [rbx+r12*8]
	cmp rdx, 1
	sbb rdx, rdx
	xor rdx, -1
	and rbp, rdx
	mov rax, QWORD PTR [rdi+176]
	or rax, rbp
	mov QWORD PTR [rdi+176], rax
	mov r11, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+128], r11
	mov r11, QWORD PTR [rsp+56]
	mov QWORD PTR [rdi+136], r11
	mov r11, QWORD PTR [rsp+48]
	mov QWORD PTR [rdi+144], r11
	mov r11, QWORD PTR [rsp+40]
	mov QWORD PTR [rdi+184], r11
	mov r11, QWORD PTR [rsp+32]
	mov QWORD PTR [rdi+192], r11
	mov r11, QWORD PTR [rsp+24]
	mov QWORD PTR [rdi+152], r11
	mov r11, QWORD PTR [rsp+16]
	mov QWORD PTR [rdi+160], r11
	mov r11, QWORD PTR [rsp+8]
	mov QWORD PTR [rdi+200], r11
	mov rbx, QWORD PTR [rsp+104]
	mov r12, QWORD PTR [rsp+96]
	mov r13, QWORD PTR [rsp+88]
	mov r14, QWORD PTR [rsp+80]
	mov r15, QWORD PTR [rsp+72]
	mov rax, QWORD PTR [rdi+176]
	and rax, 1
	pop rbp
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	ret
	.p2align 6
