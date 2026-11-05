// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_key:
	mov r11, QWORD PTR [rsp+88]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov QWORD PTR [r11+128], rdi
	mov QWORD PTR [r11+136], rsi
	mov QWORD PTR [r11+144], rdx
	mov QWORD PTR [r11+168], r8
	mov QWORD PTR [r11+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [r11+160], rax
	mov rdi, r11
	mov rcx, QWORD PTR [rdi+136]
	mov r12, rcx
	shr r12, 3
	mov QWORD PTR [rdi+48], r12
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+224], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
20:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 20b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
21:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 22f
	jmp 23f
22:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
23:
	test rdx, rdx
	jne 21b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
24:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 24b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+192]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
25:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 26f
	jmp 27f
26:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
27:
	test rdx, rdx
	jne 25b
	mov rsi, QWORD PTR [rdi+152]
	mov rcx, QWORD PTR [rdi+160]
	mov ebx, 0
28:
	ror rbx, 56
	movzx eax, BYTE PTR [rsi]
	add rbx, rax
	add rsi, 1
	sub rcx, 1
	jne 28b
	mov QWORD PTR [rdi+240], rbx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
29:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 29b
	mov r15, rbp
	mov r14, 0
210:
	mov rax, QWORD PTR [rbx+r14*8]
	mov rdx, QWORD PTR [r10+r14*8]
	xor rax, rdx
	and rax, r15
	mov rdx, QWORD PTR [rbx+r14*8]
	xor rdx, rax
	mov QWORD PTR [rbx+r14*8], rdx
	mov rdx, QWORD PTR [r10+r14*8]
	xor rdx, rax
	mov QWORD PTR [r10+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 210b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
211:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 211b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
212:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 212b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
213:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 213b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
214:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 214b
	cmp rbp, 1
	sbb rbp, rbp
	mov r15, rbp
	xor r15, -1
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
215:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 215b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ebp, 0
	mov r14, 0
216:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	mov rdx, QWORD PTR [r8+r14*8]
	add rbp, rbp
	sbb rdx, rax
	mov QWORD PTR [rsi+r14*8], rdx
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 216b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
217:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 217b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
218:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
219:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 219b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
220:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 220b
	cmp rbp, 1
	sbb rbp, rbp
	mov r15, rbp
	xor r15, -1
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
221:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 221b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov ebp, 0
	mov r14, 0
222:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	mov rdx, QWORD PTR [r8+r14*8]
	add rbp, rbp
	sbb rdx, rax
	mov QWORD PTR [rsi+r14*8], rdx
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 222b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
223:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 223b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, rdi
	add r11, 256
	mov rax, r9
	add rax, rax
	add rax, rax
	add rax, r9
	add rax, rdi
	add rax, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r9, rax
	mov r10, r12
	shr r10, 1
	sub r12, r10
	mov r13d, 0
224:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
225:
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
	jne 225b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 224b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
227:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 227b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
228:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 228b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
229:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 229b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r11, r12
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13d, 0
230:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	or rax, QWORD PTR [r10]
	and rax, 1
	sub rax, 1
	mov QWORD PTR [rdi+232], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
231:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, 1
	mov rdx, QWORD PTR [r8+r14*8+8]
	and rdx, 1
	ror rdx, 1
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 231b
	mov rbp, QWORD PTR [rdi+232]
	xor rbp, -1
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
232:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
233:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, 1
	mov rdx, QWORD PTR [r8+r14*8+8]
	and rdx, 1
	ror rdx, 1
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 233b
	mov rbp, QWORD PTR [rdi+232]
	xor rbp, -1
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
234:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 234b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
235:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, 1
	mov rdx, QWORD PTR [r8+r14*8+8]
	and rdx, 1
	ror rdx, 1
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 235b
	mov rbp, QWORD PTR [rdi+232]
	xor rbp, -1
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
236:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 236b
	add r13, 1
	cmp r13, r11
	jne 230b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	mov r15, rax
	xor r15, -1
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r14, 0
237:
	mov rax, QWORD PTR [rbx+r14*8]
	mov rdx, QWORD PTR [r10+r14*8]
	xor rax, rdx
	and rax, r15
	mov rdx, QWORD PTR [rbx+r14*8]
	xor rdx, rax
	mov QWORD PTR [rbx+r14*8], rdx
	mov rdx, QWORD PTR [r10+r14*8]
	xor rdx, rax
	mov QWORD PTR [r10+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 237b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
238:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 238b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 2
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
239:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 239b
	mov QWORD PTR [rdi+248], rbp
	xor rbp, -1
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
240:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 240b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 3
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
241:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 241b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
242:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
243:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 243b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r13, r12
	shr r13, 1
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
244:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 244b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
245:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 245b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
246:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 246b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
247:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 247b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
248:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 248b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
249:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 249b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
250:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
251:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8]
	shr rax, 1
	add rax, rax
	add rax, 1
	mov QWORD PTR [r8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
252:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 252b
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
253:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 253b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8]
	and rax, 1
	sub rax, 1
	mov r15, rax
	add r12, 1
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r14, 0
254:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 254b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rbx, QWORD PTR [r8]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov QWORD PTR [r8+80], r15
	mov eax, 1
	mov QWORD PTR [r8+24], rax
	mov r15, r13
	mov rsi, r13
	add rsi, r13
	add rsi, r13
	add rsi, 2
	mov rdi, rdi
	add rdi, 256
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
255:
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	mov rax, QWORD PTR [rax]
	mov QWORD PTR [rdi], rax
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	add rax, r9
	mov rax, QWORD PTR [rax]
	mov QWORD PTR [rdi+8], rax
	mov rbx, QWORD PTR [rdi+24]
	xor rbx, -1
	mov r14, r9
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov r9, r8
	mov r10, rcx
	mov r11, r13
	mov r12, rbp
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	xor rbx, -1
	mov QWORD PTR [rdi+24], rbx
	mov QWORD PTR [rdi+32], r9
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r11
	mov QWORD PTR [rdi+56], r12
	mov r9, r14
	mov r12, r15
	add r12, 1
	mov rcx, QWORD PTR [rdi+32]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+40]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
256:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 256b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r12, r15
	mov r14, 0
257:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 257b
	mov rdx, QWORD PTR [rbx+r14*8]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r12, 1
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+56]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
258:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 258b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r12, r15
	mov r14, 0
259:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rdx, QWORD PTR [rbx+r14*8]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r12, 1
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	mov r14, 0
260:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov rcx, QWORD PTR [rdi+32]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+40]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
261:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 261b
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov rax, QWORD PTR [r8]
	mov rcx, QWORD PTR [rdi+80]
	mul rcx
	mov rcx, rax
	mov rax, QWORD PTR [r8+r15*8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	mov eax, 0
	mov QWORD PTR [r8+r15*8+8], rax
	mov r13, r9
	mov r9, r10
	mov r12, r15
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
	mov r9, r13
	mov rax, QWORD PTR [r8+r15*8+8]
	add rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r8+r15*8+8], rax
	add r12, 1
	mov r14, 0
263:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+56]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
264:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 264b
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov rax, QWORD PTR [r8]
	mov rcx, QWORD PTR [rdi+80]
	mul rcx
	mov rcx, rax
	mov rax, QWORD PTR [r8+r15*8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	mov eax, 0
	mov QWORD PTR [r8+r15*8+8], rax
	mov r13, r9
	mov r9, r10
	mov r12, r15
	mov ebp, 0
	mov r14, 0
265:
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
	jne 265b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r9, r13
	mov rax, QWORD PTR [r8+r15*8+8]
	add rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r8+r15*8+8], rax
	add r12, 1
	mov r14, 0
266:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 266b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r14, 0
267:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	sub rsi, 1
	jne 255b
	sub rdi, 256
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	mov r13, r15
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
268:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 268b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	add r12, 1
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8+r13*8]
	shr rax, 63
	mov r15d, 0
	sub r15, rax
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r14, 0
269:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 269b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
270:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 270b
	mov r14, 0
271:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
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
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	sub rax, 1
	mov rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
273:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
	mov r11, r13
	shl r11, 4
	sub r11, r13
	add r11, 10
274:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
275:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 275b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
276:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 276b
	mov r14, 0
277:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
	sub r11, 1
	jne 274b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
278:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 278b
	mov r14, 0
279:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
280:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 280b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	add r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
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
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	mov ebp, 0
	sub rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
282:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 282b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	sub rax, 1
	mov rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
283:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
284:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 284b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
285:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 285b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
286:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 286b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov rbp, QWORD PTR [rdi+248]
	xor rbp, -1
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
287:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 287b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r11, r12
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13d, 0
	mov eax, 0
	mov r14, 0
288:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 288b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
289:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
290:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 290b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
291:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 291b
	sub r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
292:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 292b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
293:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 293b
	sub r12, 1
	mov rax, rbp
	add rax, 1
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rdx, QWORD PTR [rbx]
	add rdx, rax
	mov QWORD PTR [rbx], rdx
	add r13, 1
	cmp r13, r11
	jne 289b
	mov rax, QWORD PTR [rdi+240]
	cmp rax, 1
	jb 294f
	je 296f
	mov rax, QWORD PTR [rdi+240]
	and rax, 1
	jne 298f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2100:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2101:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2101b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2102:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2103:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2104:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2104b
	cmp rbp, 1
	sbb rbp, rbp
	mov r15, rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2105:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2105b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	mov rdx, r15
	and rdx, 1
	or rax, rdx
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2106:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2107:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r11, r12
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13d, 0
	mov eax, 0
	mov r14, 0
2108:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2108b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
2109:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2110:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2110b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
2111:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2111b
	sub r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2112:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
2113:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	sub r12, 1
	mov rax, rbp
	add rax, 1
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rdx, QWORD PTR [rbx]
	add rdx, rax
	mov QWORD PTR [rbx], rdx
	add r13, 1
	cmp r13, r11
	jne 2109b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2114:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2115:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2115b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2116:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2116b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 3
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2117:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2117b
	mov rcx, rbp
	xor rcx, -1
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, rcx
	mov QWORD PTR [rdi+248], rax
	mov rbp, rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2118:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2118b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2119:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2120:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r13, r12
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2121:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2122:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2123:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2124:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2124b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2125:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2125b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2126:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2127:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2127b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2128:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2128b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8]
	shr rax, 1
	add rax, rax
	add rax, 1
	mov QWORD PTR [r8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2129:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2130:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2130b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8]
	and rax, 1
	sub rax, 1
	mov r15, rax
	add r12, 1
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r14, 0
2131:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2131b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rbx, QWORD PTR [r8]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov QWORD PTR [r8+80], r15
	mov eax, 1
	mov QWORD PTR [r8+24], rax
	mov r15, r13
	mov rsi, r13
	add rsi, r13
	add rsi, r13
	add rsi, 2
	mov rdi, rdi
	add rdi, 256
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
2132:
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	mov rax, QWORD PTR [rax]
	mov QWORD PTR [rdi], rax
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	add rax, r9
	mov rax, QWORD PTR [rax]
	mov QWORD PTR [rdi+8], rax
	mov rbx, QWORD PTR [rdi+24]
	xor rbx, -1
	mov r14, r9
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov r9, r8
	mov r10, rcx
	mov r11, r13
	mov r12, rbp
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	xor rbx, -1
	mov QWORD PTR [rdi+24], rbx
	mov QWORD PTR [rdi+32], r9
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r11
	mov QWORD PTR [rdi+56], r12
	mov r9, r14
	mov r12, r15
	add r12, 1
	mov rcx, QWORD PTR [rdi+32]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+40]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2133:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r12, r15
	mov r14, 0
2134:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov rdx, QWORD PTR [rbx+r14*8]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r12, 1
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+56]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2135:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2135b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r12, r15
	mov r14, 0
2136:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2136b
	mov rdx, QWORD PTR [rbx+r14*8]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r12, 1
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	mov r14, 0
2137:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2137b
	mov rcx, QWORD PTR [rdi+32]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+40]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2138:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov rax, QWORD PTR [r8]
	mov rcx, QWORD PTR [rdi+80]
	mul rcx
	mov rcx, rax
	mov rax, QWORD PTR [r8+r15*8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	mov eax, 0
	mov QWORD PTR [r8+r15*8+8], rax
	mov r13, r9
	mov r9, r10
	mov r12, r15
	mov ebp, 0
	mov r14, 0
2139:
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
	jne 2139b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r9, r13
	mov rax, QWORD PTR [r8+r15*8+8]
	add rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r8+r15*8+8], rax
	add r12, 1
	mov r14, 0
2140:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2140b
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+56]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2141:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2141b
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov rax, QWORD PTR [r8]
	mov rcx, QWORD PTR [rdi+80]
	mul rcx
	mov rcx, rax
	mov rax, QWORD PTR [r8+r15*8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	mov eax, 0
	mov QWORD PTR [r8+r15*8+8], rax
	mov r13, r9
	mov r9, r10
	mov r12, r15
	mov ebp, 0
	mov r14, 0
2142:
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
	jne 2142b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r9, r13
	mov rax, QWORD PTR [r8+r15*8+8]
	add rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r8+r15*8+8], rax
	add r12, 1
	mov r14, 0
2143:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2143b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r14, 0
2144:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	sub rsi, 1
	jne 2132b
	sub rdi, 256
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	mov r13, r15
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2145:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2145b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	add r12, 1
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8+r13*8]
	shr rax, 63
	mov r15d, 0
	sub r15, rax
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r14, 0
2146:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2147:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2147b
	mov r14, 0
2148:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2149:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	sub rax, 1
	mov rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2150:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov r11, r13
	shl r11, 4
	sub r11, r13
	add r11, 10
2151:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2152:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2153:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2153b
	mov r14, 0
2154:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2154b
	sub r11, 1
	jne 2151b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2155:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2155b
	mov r14, 0
2156:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2157:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	add r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2158:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2158b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	mov ebp, 0
	sub rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2159:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	sub rax, 1
	mov rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2160:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2160b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2161:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2162:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2163:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2163b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2164:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2165:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2165b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2166:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2166b
	jmp 299f
298:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2167:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2167b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2168:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2169:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r11, r12
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13d, 0
	mov eax, 0
	mov r14, 0
2170:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2170b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
2171:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2172:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2172b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
2173:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2173b
	sub r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2174:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2174b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
2175:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2175b
	sub r12, 1
	mov rax, rbp
	add rax, 1
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rdx, QWORD PTR [rbx]
	add rdx, rax
	mov QWORD PTR [rbx], rdx
	add r13, 1
	cmp r13, r11
	jne 2171b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2176:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2176b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2177:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2177b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r13d, 1
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2178:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2178b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2179:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2179b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2180:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2180b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2181:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2182:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2183:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2184:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2184b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2185:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2185b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8]
	shr rax, 1
	add rax, rax
	add rax, 1
	mov QWORD PTR [r8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2186:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2186b
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2187:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2187b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8]
	and rax, 1
	sub rax, 1
	mov r15, rax
	add r12, 1
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r14, 0
2188:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2188b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rbx, QWORD PTR [r8]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov QWORD PTR [r8+80], r15
	mov eax, 1
	mov QWORD PTR [r8+24], rax
	mov r15, r13
	mov rsi, r13
	add rsi, r13
	add rsi, r13
	add rsi, 2
	mov rdi, rdi
	add rdi, 256
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
2189:
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	mov rax, QWORD PTR [rax]
	mov QWORD PTR [rdi], rax
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	add rax, r9
	mov rax, QWORD PTR [rax]
	mov QWORD PTR [rdi+8], rax
	mov rbx, QWORD PTR [rdi+24]
	xor rbx, -1
	mov r14, r9
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov r9, r8
	mov r10, rcx
	mov r11, r13
	mov r12, rbp
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	xor rbx, -1
	mov QWORD PTR [rdi+24], rbx
	mov QWORD PTR [rdi+32], r9
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r11
	mov QWORD PTR [rdi+56], r12
	mov r9, r14
	mov r12, r15
	add r12, 1
	mov rcx, QWORD PTR [rdi+32]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+40]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2190:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2190b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r12, r15
	mov r14, 0
2191:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2191b
	mov rdx, QWORD PTR [rbx+r14*8]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r12, 1
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+56]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2192:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2192b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r12, r15
	mov r14, 0
2193:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2193b
	mov rdx, QWORD PTR [rbx+r14*8]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r12, 1
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	mov r14, 0
2194:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2194b
	mov rcx, QWORD PTR [rdi+32]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+40]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2195:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2195b
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov rax, QWORD PTR [r8]
	mov rcx, QWORD PTR [rdi+80]
	mul rcx
	mov rcx, rax
	mov rax, QWORD PTR [r8+r15*8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	mov eax, 0
	mov QWORD PTR [r8+r15*8+8], rax
	mov r13, r9
	mov r9, r10
	mov r12, r15
	mov ebp, 0
	mov r14, 0
2196:
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
	jne 2196b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r9, r13
	mov rax, QWORD PTR [r8+r15*8+8]
	add rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r8+r15*8+8], rax
	add r12, 1
	mov r14, 0
2197:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2197b
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+56]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2198:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2198b
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov rax, QWORD PTR [r8]
	mov rcx, QWORD PTR [rdi+80]
	mul rcx
	mov rcx, rax
	mov rax, QWORD PTR [r8+r15*8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	mov eax, 0
	mov QWORD PTR [r8+r15*8+8], rax
	mov r13, r9
	mov r9, r10
	mov r12, r15
	mov ebp, 0
	mov r14, 0
2199:
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
	jne 2199b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r9, r13
	mov rax, QWORD PTR [r8+r15*8+8]
	add rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r8+r15*8+8], rax
	add r12, 1
	mov r14, 0
2200:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2200b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r14, 0
2201:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2201b
	sub rsi, 1
	jne 2189b
	sub rdi, 256
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	mov r13, r15
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2202:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2202b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	add r12, 1
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8+r13*8]
	shr rax, 63
	mov r15d, 0
	sub r15, rax
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r14, 0
2203:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2203b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2204:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2204b
	mov r14, 0
2205:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2205b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2206:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2206b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	sub rax, 1
	mov rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2207:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2207b
	mov r11, r13
	shl r11, 4
	sub r11, r13
	add r11, 10
2208:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2209:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2209b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2210:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2210b
	mov r14, 0
2211:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2211b
	sub r11, 1
	jne 2208b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2212:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2212b
	mov r14, 0
2213:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2213b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2214:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2214b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	add r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2215:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2215b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	mov ebp, 0
	sub rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2216:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2216b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	sub rax, 1
	mov rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2217:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2217b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2218:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2218b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2219:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2219b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2220:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2220b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 2
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2221:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2221b
	xor rbp, -1
	mov QWORD PTR [rdi+248], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2223:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2223b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rbp
	mov rbx, QWORD PTR [rdi+240]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, rdi
	add r10, 256
	mov rsi, QWORD PTR [rdi+240]
	sub rsi, QWORD PTR [rbx]
	mov rax, QWORD PTR [r10]
	mul rsi
	add rax, 1
	mul rcx
	mov r15, rax
	mov QWORD PTR [rdi+232], rsi
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2224:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2224b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov QWORD PTR [r8], r15
	mov rax, r9
	add rax, rax
	add rax, rax
	add rax, r9
	add rax, rax
	add rax, r9
	add rax, rdi
	add rax, 256
	mov r9, rax
	mov rcx, QWORD PTR [rdi+232]
	mov ebp, 0
	mov r14, 0
2225:
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
	jne 2225b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
299:
	jmp 297f
296:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2227:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2227b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+248], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2228:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2228b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
297:
	jmp 295f
294:
	mov eax, 0
	mov QWORD PTR [rdi+248], rax
295:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2229:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2229b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rax, r12
	shr rax, 1
	mov edx, 1
	mov QWORD PTR [rbx+rax*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2230:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2230b
	and rbp, QWORD PTR [rdi+248]
	test rbp, rbp
	jne 2231f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2233:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2233b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2234:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2234b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2235:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2235b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 3
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2236:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2236b
	mov rcx, rbp
	xor rcx, -1
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, rcx
	mov rbp, rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2237:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2237b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2238:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2238b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2239:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2239b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r13, r12
	shr r13, 1
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2240:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2240b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2241:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2241b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2242:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2242b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2243:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2243b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2244:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2244b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2245:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2245b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2246:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2246b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2247:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2247b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8]
	shr rax, 1
	add rax, rax
	add rax, 1
	mov QWORD PTR [r8], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2248:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2248b
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2249:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2249b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8]
	and rax, 1
	sub rax, 1
	mov r15, rax
	add r12, 1
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r14, 0
2250:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2250b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rbx, QWORD PTR [r8]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov QWORD PTR [r8+80], r15
	mov eax, 1
	mov QWORD PTR [r8+24], rax
	mov r15, r13
	mov rsi, r13
	add rsi, r13
	add rsi, r13
	add rsi, 2
	mov rdi, rdi
	add rdi, 256
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
	add rdi, r9
2251:
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	mov rax, QWORD PTR [rax]
	mov QWORD PTR [rdi], rax
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	add rax, r9
	mov rax, QWORD PTR [rax]
	mov QWORD PTR [rdi+8], rax
	mov rbx, QWORD PTR [rdi+24]
	xor rbx, -1
	mov r14, r9
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov r9, r8
	mov r10, rcx
	mov r11, r13
	mov r12, rbp
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi]
	mul r8
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+8]
	mul rcx
	add rax, QWORD PTR [rdi+16]
	shr rax, 15
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi]
	mul r13
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+8]
	mul rbp
	add rax, QWORD PTR [rdi]
	shr rax, 15
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	mov r8, QWORD PTR [rdi]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+8]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+16]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+16], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+16]
	mov r12, rax
	xor rbx, -1
	mov QWORD PTR [rdi+24], rbx
	mov QWORD PTR [rdi+32], r9
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r11
	mov QWORD PTR [rdi+56], r12
	mov r9, r14
	mov r12, r15
	add r12, 1
	mov rcx, QWORD PTR [rdi+32]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+40]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2252:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2252b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r12, r15
	mov r14, 0
2253:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2253b
	mov rdx, QWORD PTR [rbx+r14*8]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r12, 1
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+56]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2254:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2254b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r12, r15
	mov r14, 0
2255:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2255b
	mov rdx, QWORD PTR [rbx+r14*8]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r12, 1
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	mov r14, 0
2256:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2256b
	mov rcx, QWORD PTR [rdi+32]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+40]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2257:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2257b
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov rax, QWORD PTR [r8]
	mov rcx, QWORD PTR [rdi+80]
	mul rcx
	mov rcx, rax
	mov rax, QWORD PTR [r8+r15*8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	mov eax, 0
	mov QWORD PTR [r8+r15*8+8], rax
	mov r13, r9
	mov r9, r10
	mov r12, r15
	mov ebp, 0
	mov r14, 0
2258:
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
	jne 2258b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r9, r13
	mov rax, QWORD PTR [r8+r15*8+8]
	add rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r8+r15*8+8], rax
	add r12, 1
	mov r14, 0
2259:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2259b
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov rbp, QWORD PTR [rdi+56]
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+64]
	mov rax, rbp
	and rax, QWORD PTR [rdi+72]
	add r8, rax
	mov r13d, 0
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov r14, 0
2260:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [r10+r14*8]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [r11+r14*8], r8
	mov r8, r13
	mov r13d, 0
	add r14, 1
	cmp r14, r12
	jne 2260b
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r11, rdi
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	add r11, r9
	mov rax, QWORD PTR [r8]
	mov rcx, QWORD PTR [rdi+80]
	mul rcx
	mov rcx, rax
	mov rax, QWORD PTR [r8+r15*8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+64], rdx
	mov eax, 0
	mov QWORD PTR [r8+r15*8+8], rax
	mov r13, r9
	mov r9, r10
	mov r12, r15
	mov ebp, 0
	mov r14, 0
2261:
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
	jne 2261b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r9, r13
	mov rax, QWORD PTR [r8+r15*8+8]
	add rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r8+r15*8+8], rax
	add r12, 1
	mov r14, 0
2262:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2262b
	mov rbx, rdi
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	add rbx, r9
	mov r10, rdi
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	add r10, r9
	mov r14, 0
2263:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2263b
	sub rsi, 1
	jne 2251b
	sub rdi, 256
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	sub rdi, r9
	mov r13, r15
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2264:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2264b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	add r12, 1
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rax, QWORD PTR [r8+r13*8]
	shr rax, 63
	mov r15d, 0
	sub r15, rax
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r14, 0
2265:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2265b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2266:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2266b
	mov r14, 0
2267:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2267b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2268:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2268b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	sub rax, 1
	mov rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2269:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2269b
	mov r11, r13
	shl r11, 4
	sub r11, r13
	add r11, 10
2270:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2271:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2271b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2272:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2272b
	mov r14, 0
2273:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2273b
	sub r11, 1
	jne 2270b
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2274:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2274b
	mov r14, 0
2275:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2275b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2276:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2276b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	add r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2277:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2277b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	mov ebp, 0
	sub rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2278:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2278b
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r13*8]
	shr rax, 63
	sub rax, 1
	mov rbp, rax
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2279:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2279b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2280:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2280b
	mov r12, r9
	shr r12, 3
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2281:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2281b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2282:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2282b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2283:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2283b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2284:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2284b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2285:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2285b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2286:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2286b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2287:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2287b
	cmp rbp, 1
	sbb rbp, rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	and rbp, 1
	or rax, rbp
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2288:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2288b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2289:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2289b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r11, r12
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13d, 0
	mov eax, 0
	mov r14, 0
2290:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2290b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
2291:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2292:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2292b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
2293:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2293b
	sub r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2294:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2294b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
2295:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2295b
	sub r12, 1
	mov rax, rbp
	add rax, 1
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rdx, QWORD PTR [rbx]
	add rdx, rax
	mov QWORD PTR [rbx], rdx
	add r13, 1
	cmp r13, r11
	jne 2291b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2297:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2297b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2298:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2298b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2299:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2299b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2300:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2300b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2301:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2301b
	cmp rbp, 1
	sbb rbp, rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	and rbp, 1
	or rax, rbp
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2302:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2302b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2303:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2303b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r11, r12
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13d, 0
	mov eax, 0
	mov r14, 0
2304:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2304b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
2305:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2306:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2306b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
2307:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2307b
	sub r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2308:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2308b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
2309:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2309b
	sub r12, 1
	mov rax, rbp
	add rax, 1
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rdx, QWORD PTR [rbx]
	add rdx, rax
	mov QWORD PTR [rbx], rdx
	add r13, 1
	cmp r13, r11
	jne 2305b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2310:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2310b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r11, rdi
	add r11, 256
	mov rax, r9
	add rax, rdi
	add rax, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r9, rax
	mov r10, r12
	shr r10, 1
	sub r12, r10
	mov r13d, 0
2311:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2312:
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
	jne 2312b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 2311b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx+r12*8-8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	and rdx, QWORD PTR [rdi+248]
	mov rcx, rdx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rcx, rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rcx, rax
	mov rax, QWORD PTR [rdi+240]
	and rax, 1
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	mov rax, QWORD PTR [rdi+240]
	cmp rax, 3
	sbb rdx, rdx
	xor rdx, -1
	and rcx, rdx
	mov rax, QWORD PTR [rdi+240]
	shr rax, 33
	cmp rax, 1
	sbb rdx, rdx
	and rcx, rdx
	mov QWORD PTR [rdi+248], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+136]
	mov r15, QWORD PTR [rdi+248]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2313:
	mov rbp, rdx
	and rbp, 7
	je 2314f
	jmp 2315f
2314:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2315:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2313b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+144]
	mov rcx, QWORD PTR [rdi+136]
	mov r15, QWORD PTR [rdi+248]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2316:
	mov rbp, rdx
	and rbp, 7
	je 2317f
	jmp 2318f
2317:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2318:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2316b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+184]
	mov r15, QWORD PTR [rdi+248]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2319:
	mov rbp, rdx
	and rbp, 7
	je 2320f
	jmp 2321f
2320:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2321:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2319b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+192]
	mov rcx, QWORD PTR [rdi+184]
	mov r15, QWORD PTR [rdi+248]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2322:
	mov rbp, rdx
	and rbp, 7
	je 2323f
	jmp 2324f
2323:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2324:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2322b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+184]
	mov r15, QWORD PTR [rdi+248]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2325:
	mov rbp, rdx
	and rbp, 7
	je 2326f
	jmp 2327f
2326:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2327:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2325b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+208]
	mov rcx, QWORD PTR [rdi+184]
	mov r15, QWORD PTR [rdi+248]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2328:
	mov rbp, rdx
	and rbp, 7
	je 2329f
	jmp 2330f
2329:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2330:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2328b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+216]
	mov rcx, QWORD PTR [rdi+184]
	mov r15, QWORD PTR [rdi+248]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2331:
	mov rbp, rdx
	and rbp, 7
	je 2332f
	jmp 2333f
2332:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2333:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2331b
	mov rax, QWORD PTR [rdi+248]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 2232f
2231:
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+136]
	mov eax, 0
2334:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2334b
	mov rsi, QWORD PTR [rdi+144]
	mov rcx, QWORD PTR [rdi+136]
	mov eax, 0
2335:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2335b
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
2336:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2336b
	mov rsi, QWORD PTR [rdi+192]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
2337:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2337b
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
2338:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2338b
	mov rsi, QWORD PTR [rdi+208]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
2339:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2339b
	mov rsi, QWORD PTR [rdi+216]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
2340:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2340b
	mov eax, 2
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
2232:
	ret
	.p2align 6

vg_rsa_prime_search_init:
	cmp rsi, 32
	jb 20f
	cmp rsi, 513
	jae 22f
	mov rax, rsi
	and rax, 7
	jne 24f
	test rcx, rcx
	je 26f
	cmp rcx, 9
	jae 28f
	mov r9d, 0
	mov r11, rcx
	sub r11, 1
	test r11, r11
	je 210f
212:
	movzx eax, BYTE PTR [rdx]
	or r9, rax
	add rdx, 1
	sub r11, 1
	jne 212b
	jmp 211f
210:
211:
	movzx eax, BYTE PTR [rdx]
	xor rax, 3
	or rax, r9
	mov r9, rax
	mov rax, rsi
	shl rax, 3
	mov rcx, rax
	shl rax, 2
	add rax, rcx
	mov rcx, rsi
	shl rcx, 6
	test r9, r9
	cmove rax, rcx
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rsi
	mov rax, rsi
	shl rax, 15
	add rax, rsi
	mov QWORD PTR [rdi+16], rax
	mov rax, rsi
	shl rax, 5
	mov QWORD PTR [rdi+24], rax
	mov eax, 1
	jmp 29f
28:
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
29:
	jmp 27f
26:
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
27:
	jmp 25f
24:
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
25:
	jmp 23f
22:
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
23:
	jmp 21f
20:
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
21:
	ret
	.p2align 6

vg_rsa_prime_search_adx:
	lea rsp, [rsp-160]
	mov QWORD PTR [rsp+32], r12
	mov r12, rsp
	mov QWORD PTR [r12+40], rdi
	mov QWORD PTR [r12+48], rsi
	mov QWORD PTR [r12+56], rdx
	mov QWORD PTR [r12+64], rcx
	mov QWORD PTR [r12+72], r8
	mov QWORD PTR [r12+80], r9
	mov rax, QWORD PTR [rsp+168]
	mov QWORD PTR [r12+88], rax
	mov rax, QWORD PTR [rsp+176]
	mov QWORD PTR [r12+96], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [r12+104], rax
	mov rax, QWORD PTR [rsp+192]
	mov QWORD PTR [r12+112], rax
	mov rax, QWORD PTR [rsp+200]
	mov QWORD PTR [r12+120], rax
	mov rax, QWORD PTR [rsp+208]
	mov QWORD PTR [r12+144], rax
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [r12], rcx
	mov QWORD PTR [r12+8], rsi
	mov rcx, rsi
	shl rcx, 15
	add rcx, rsi
	mov QWORD PTR [r12+16], rcx
	mov eax, 0
	mov QWORD PTR [r12+24], rax
	mov QWORD PTR [r12+128], rax
20:
	mov rax, QWORD PTR [r12]
	test rax, rax
	je 21f
	lea rsp, [rsp-40]
	mov rdi, QWORD PTR [r12+40]
	mov rsi, QWORD PTR [r12+48]
	mov rdx, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+64]
	mov r8, QWORD PTR [r12+72]
	mov r9, QWORD PTR [r12+80]
	mov rax, QWORD PTR [r12+88]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [r12+96]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [r12+104]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [r12+112]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [r12+120]
	mov QWORD PTR [rsp+32], rax
	call {vg_rsa_keygen_candidate_adx}
	lea rsp, [rsp+40]
	mov eax, eax
	cmp rax, 1
	je 23f
	test rax, rax
	je 25f
	mov rdx, rax
	mov rcx, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rcx]
	test rcx, rcx
	je 27f
	mov rax, QWORD PTR [r12+96]
	add rax, rcx
	mov QWORD PTR [r12+96], rax
	mov rax, QWORD PTR [r12+104]
	sub rax, rcx
	mov QWORD PTR [r12+104], rax
	mov rax, QWORD PTR [r12+128]
	add rax, rcx
	mov QWORD PTR [r12+128], rax
	mov eax, 4
	mov QWORD PTR [r12+136], rax
	cmp rdx, 2
	je 29f
	mov rax, QWORD PTR [r12]
	sub rax, 1
	mov QWORD PTR [r12], rax
	jmp 210f
29:
210:
	jmp 28f
27:
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 3
	mov QWORD PTR [r12+136], rax
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+40]
	mov rcx, QWORD PTR [rdi+48]
	mov eax, 0
211:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 211b
28:
	jmp 26f
25:
	mov rax, QWORD PTR [r12+104]
	cmp rax, QWORD PTR [r12+16]
	jae 212f
	mov rcx, QWORD PTR [r12+8]
	shl rcx, 4
	cmp rax, rcx
	cmovb rax, rcx
	shl rax, 1
	mov rcx, QWORD PTR [r12+16]
	cmp rax, rcx
	cmovae rax, rcx
	mov QWORD PTR [r12+24], rax
	mov eax, 0
	mov QWORD PTR [r12+136], rax
	jmp 213f
212:
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 3
	mov QWORD PTR [r12+136], rax
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+40]
	mov rcx, QWORD PTR [rdi+48]
	mov eax, 0
214:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 214b
213:
26:
	jmp 24f
23:
	mov rcx, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rcx]
	mov rax, QWORD PTR [r12+128]
	add rax, rcx
	mov QWORD PTR [r12+128], rax
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 1
	mov QWORD PTR [r12+136], rax
24:
	jmp 22f
21:
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 3
	mov QWORD PTR [r12+136], rax
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+40]
	mov rcx, QWORD PTR [rdi+48]
	mov eax, 0
215:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 215b
22:
	mov rax, QWORD PTR [r12+136]
	cmp rax, 4
	je 20b
	mov rax, QWORD PTR [r12+144]
	mov rcx, QWORD PTR [r12]
	mov rdx, QWORD PTR [r12+8]
	mov rsi, QWORD PTR [r12+16]
	mov rdi, QWORD PTR [r12+24]
	mov r8, QWORD PTR [r12+56]
	mov r9, QWORD PTR [r12+128]
	mov r10, QWORD PTR [r12+136]
	mov r11, QWORD PTR [r12+32]
	mov QWORD PTR [rax], rcx
	mov QWORD PTR [rax+8], rdx
	mov QWORD PTR [rax+16], rsi
	mov QWORD PTR [rax+24], rdi
	mov QWORD PTR [r8], r9
	mov rax, r10
	mov r12, r11
	lea rsp, [rsp+160]
	ret
	.p2align 6

vg_rsa_prime_search:
	lea rsp, [rsp-160]
	mov QWORD PTR [rsp+32], r12
	mov r12, rsp
	mov QWORD PTR [r12+40], rdi
	mov QWORD PTR [r12+48], rsi
	mov QWORD PTR [r12+56], rdx
	mov QWORD PTR [r12+64], rcx
	mov QWORD PTR [r12+72], r8
	mov QWORD PTR [r12+80], r9
	mov rax, QWORD PTR [rsp+168]
	mov QWORD PTR [r12+88], rax
	mov rax, QWORD PTR [rsp+176]
	mov QWORD PTR [r12+96], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [r12+104], rax
	mov rax, QWORD PTR [rsp+192]
	mov QWORD PTR [r12+112], rax
	mov rax, QWORD PTR [rsp+200]
	mov QWORD PTR [r12+120], rax
	mov rax, QWORD PTR [rsp+208]
	mov QWORD PTR [r12+144], rax
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [r12], rcx
	mov QWORD PTR [r12+8], rsi
	mov rcx, rsi
	shl rcx, 15
	add rcx, rsi
	mov QWORD PTR [r12+16], rcx
	mov eax, 0
	mov QWORD PTR [r12+24], rax
	mov QWORD PTR [r12+128], rax
20:
	mov rax, QWORD PTR [r12]
	test rax, rax
	je 21f
	lea rsp, [rsp-40]
	mov rdi, QWORD PTR [r12+40]
	mov rsi, QWORD PTR [r12+48]
	mov rdx, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+64]
	mov r8, QWORD PTR [r12+72]
	mov r9, QWORD PTR [r12+80]
	mov rax, QWORD PTR [r12+88]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [r12+96]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [r12+104]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [r12+112]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [r12+120]
	mov QWORD PTR [rsp+32], rax
	call {vg_rsa_keygen_candidate}
	lea rsp, [rsp+40]
	mov eax, eax
	cmp rax, 1
	je 23f
	test rax, rax
	je 25f
	mov rdx, rax
	mov rcx, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rcx]
	test rcx, rcx
	je 27f
	mov rax, QWORD PTR [r12+96]
	add rax, rcx
	mov QWORD PTR [r12+96], rax
	mov rax, QWORD PTR [r12+104]
	sub rax, rcx
	mov QWORD PTR [r12+104], rax
	mov rax, QWORD PTR [r12+128]
	add rax, rcx
	mov QWORD PTR [r12+128], rax
	mov eax, 4
	mov QWORD PTR [r12+136], rax
	cmp rdx, 2
	je 29f
	mov rax, QWORD PTR [r12]
	sub rax, 1
	mov QWORD PTR [r12], rax
	jmp 210f
29:
210:
	jmp 28f
27:
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 3
	mov QWORD PTR [r12+136], rax
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+40]
	mov rcx, QWORD PTR [rdi+48]
	mov eax, 0
211:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 211b
28:
	jmp 26f
25:
	mov rax, QWORD PTR [r12+104]
	cmp rax, QWORD PTR [r12+16]
	jae 212f
	mov rcx, QWORD PTR [r12+8]
	shl rcx, 4
	cmp rax, rcx
	cmovb rax, rcx
	shl rax, 1
	mov rcx, QWORD PTR [r12+16]
	cmp rax, rcx
	cmovae rax, rcx
	mov QWORD PTR [r12+24], rax
	mov eax, 0
	mov QWORD PTR [r12+136], rax
	jmp 213f
212:
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 3
	mov QWORD PTR [r12+136], rax
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+40]
	mov rcx, QWORD PTR [rdi+48]
	mov eax, 0
214:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 214b
213:
26:
	jmp 24f
23:
	mov rcx, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rcx]
	mov rax, QWORD PTR [r12+128]
	add rax, rcx
	mov QWORD PTR [r12+128], rax
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 1
	mov QWORD PTR [r12+136], rax
24:
	jmp 22f
21:
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 3
	mov QWORD PTR [r12+136], rax
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+40]
	mov rcx, QWORD PTR [rdi+48]
	mov eax, 0
215:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 215b
22:
	mov rax, QWORD PTR [r12+136]
	cmp rax, 4
	je 20b
	mov rax, QWORD PTR [r12+144]
	mov rcx, QWORD PTR [r12]
	mov rdx, QWORD PTR [r12+8]
	mov rsi, QWORD PTR [r12+16]
	mov rdi, QWORD PTR [r12+24]
	mov r8, QWORD PTR [r12+56]
	mov r9, QWORD PTR [r12+128]
	mov r10, QWORD PTR [r12+136]
	mov r11, QWORD PTR [r12+32]
	mov QWORD PTR [rax], rcx
	mov QWORD PTR [rax+8], rdx
	mov QWORD PTR [rax+16], rsi
	mov QWORD PTR [rax+24], rdi
	mov QWORD PTR [r8], r9
	mov rax, r10
	mov r12, r11
	lea rsp, [rsp+160]
	ret
	.p2align 6
