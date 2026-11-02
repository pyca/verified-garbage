// The functions of `src/internal/vg_rsa_private_crt_ifma.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_crt_ifma:
	mov r11, QWORD PTR [rsp+88]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov QWORD PTR [r11+128], rdi
	mov QWORD PTR [r11+136], rdx
	mov QWORD PTR [r11+144], rcx
	mov QWORD PTR [r11+168], r8
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11+160], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [r11+224], rax
	mov rdi, r11
	mov rdx, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	movzx eax, BYTE PTR [rdx]
	cmp rax, 1
	sbb rbp, rbp
	movzx eax, BYTE PTR [rdx+rcx*1-1]
	and rax, 1
	cmp rax, 1
	sbb rsi, rsi
	or rbp, rsi
	mov rsi, rcx
	sub rsi, 64
	ror rsi, 56
	movzx eax, BYTE PTR [rdx]
	add rsi, rax
	cmp rsi, 128
	sbb rsi, rsi
	or rbp, rsi
	test rbp, rbp
	jne 20f
	mov rcx, QWORD PTR [rdi+144]
	mov r12, rcx
	add r12, 7
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
	mov rsi, QWORD PTR [rdi+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
22:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 23f
	jmp 24f
23:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
24:
	test rdx, rdx
	jne 22b
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+144]
	mov rbx, QWORD PTR [rdi+72]
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
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
28:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 28b
	mov QWORD PTR [rdi+176], rbp
	mov rbx, QWORD PTR [r10]
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
	mov QWORD PTR [rdi+56], r15
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
29:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 29b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 210f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 212f
214:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 214b
	jmp 213f
212:
213:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
215:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 215b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
216:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
217:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 217b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
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
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 216b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
220:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 220b
	jmp 211f
210:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
221:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 221b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
222:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 222b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
223:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
224:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 224b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
225:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 225b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
226:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
227:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 227b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 223b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
228:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 228b
211:
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rdx, rdi
	mov rax, QWORD PTR [rdx+120]
	mov rdx, QWORD PTR [rdx+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+232], rax
	mov r12, QWORD PTR [rdi+160]
	add r12, 7
	shr r12, 3
	cmp r12, 2
	jb 229f
	jmp 230f
229:
	mov r12d, 2
230:
	mov rsi, rdi
	mov rdi, rax
	mov QWORD PTR [rdi+128], rsi
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
	mov rdi, rsi
	mov rdx, QWORD PTR [rdi+232]
	mov rax, QWORD PTR [rdx+120]
	mov rdx, QWORD PTR [rdx+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+240], rax
	mov r12, QWORD PTR [rdi+192]
	add r12, 7
	shr r12, 3
	cmp r12, 2
	jb 231f
	jmp 232f
231:
	mov r12d, 2
232:
	mov rsi, rdi
	mov rdi, rax
	mov QWORD PTR [rdi+128], rsi
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
	mov rdi, rsi
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
233:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 233b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+152]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
234:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 235f
	jmp 236f
235:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
236:
	test rdx, rdx
	jne 234b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
237:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 237b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+224]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
238:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 239f
	jmp 240f
239:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
240:
	test rdx, rdx
	jne 238b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
241:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 241b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+184]
	mov rcx, QWORD PTR [rax+192]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
242:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 243f
	jmp 244f
243:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
244:
	test rdx, rdx
	jne 242b
	mov rdi, QWORD PTR [rdi+128]
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
245:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 245b
	mov rax, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rax+64]
	mov r10, QWORD PTR [rax+48]
	mov rax, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rax+64]
	mov r12, QWORD PTR [rax+48]
	mov r8, QWORD PTR [rdi+80]
	mov r13d, 0
246:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
247:
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
	jne 247b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 246b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+80]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
248:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 248b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	add r12, 2
	mov r14, 0
249:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 249b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov rdi, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
250:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 250b
	mov rax, QWORD PTR [rdi+128]
	and rbp, QWORD PTR [rax+176]
	mov QWORD PTR [rax+176], rbp
	mov rax, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rax+176]
	mov QWORD PTR [rdi+192], rax
	mov r15, QWORD PTR [rdi+192]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+64]
	mov r14, 0
251:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
	mov rax, r15
	xor rax, -1
	and rax, 3
	or rax, QWORD PTR [rbx]
	mov QWORD PTR [rbx], rax
	mov rbx, rax
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
	mov QWORD PTR [rdi+56], r15
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
252:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 252b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rax+176]
	mov QWORD PTR [rdi+192], rax
	mov r15, QWORD PTR [rdi+192]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+64]
	mov r14, 0
253:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 253b
	mov rax, r15
	xor rax, -1
	and rax, 3
	or rax, QWORD PTR [rbx]
	mov QWORD PTR [rbx], rax
	mov rbx, rax
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
	mov QWORD PTR [rdi+56], r15
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
254:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+48]
	xor rax, 32
	mov rdx, QWORD PTR [rdi+160]
	add rdx, 7
	shr rdx, 3
	xor rdx, 16
	or rax, rdx
	mov rdx, QWORD PTR [rdi+192]
	add rdx, 7
	shr rdx, 3
	xor rdx, 16
	or rax, rdx
	je 255f
	mov rax, QWORD PTR [rdi+48]
	xor rax, 48
	mov rdx, QWORD PTR [rdi+160]
	add rdx, 7
	shr rdx, 3
	xor rdx, 24
	or rax, rdx
	mov rdx, QWORD PTR [rdi+192]
	add rdx, 7
	shr rdx, 3
	xor rdx, 24
	or rax, rdx
	je 257f
	mov rax, QWORD PTR [rdi+48]
	xor rax, 64
	mov rdx, QWORD PTR [rdi+160]
	add rdx, 7
	shr rdx, 3
	xor rdx, 32
	or rax, rdx
	mov rdx, QWORD PTR [rdi+192]
	add rdx, 7
	shr rdx, 3
	xor rdx, 32
	or rax, rdx
	jmp 258f
257:
258:
	jmp 256f
255:
256:
	je 259f
	mov rax, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [rax+48]
	mov r12, QWORD PTR [rdi+48]
	mov ecx, 0
261:
	add rcx, rax
	cmp rcx, r12
	jb 261b
	add rcx, rax
	sub rcx, r12
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+248], rcx
	mov rax, rcx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	jne 262f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 264f
266:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 266b
	jmp 265f
264:
265:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
267:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 268f
	jmp 269f
268:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
270:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 270b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
271:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 271b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
272:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
269:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 267b
	jmp 263f
262:
	mov rcx, QWORD PTR [rdi+248]
	shr rcx, 6
	mov rdx, r12
	sub rdx, 1
	cmp rcx, rdx
	jb 273f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 275f
277:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 277b
	jmp 276f
275:
276:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
278:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 279f
	jmp 280f
279:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
281:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 281b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
282:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 282b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
283:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
280:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 278b
	jmp 274f
273:
	mov edx, 1
	mov r8, QWORD PTR [rdi+112]
	mov eax, 0
	mov r14, 0
284:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 284b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
274:
263:
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
285:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 285b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
286:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
287:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 287b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 288f
	mov r12, QWORD PTR [rdi+48]
	jmp 289f
288:
289:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
290:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 290b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
291:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 291b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
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
	sbb rbp, rbp
	mov r14, 0
293:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 293b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 286b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
294:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 294b
	mov rdi, QWORD PTR [rdi+128]
	mov edx, 6
	mov ecx, 5
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
295:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 295b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
296:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
297:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 298f
	mov r12, QWORD PTR [rdi+48]
	jmp 299f
298:
299:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2100:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2101:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2101b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2102:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2103:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 296b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+216]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+192]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2104:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2105:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2105b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2106:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2107:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2108:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2108b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2107b
2109:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2110:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2111:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
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
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
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
2112:
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
	jne 2112b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 2111b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2110b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2109b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+232]
	mov rax, QWORD PTR [rax+48]
	mov r12, QWORD PTR [rdi+48]
	mov ecx, 0
2113:
	add rcx, rax
	cmp rcx, r12
	jb 2113b
	add rcx, rax
	sub rcx, r12
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+248], rcx
	mov rax, rcx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	jne 2114f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2116f
2118:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2118b
	jmp 2117f
2116:
2117:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
2119:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 2120f
	jmp 2121f
2120:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2122:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2123:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2124:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2124b
2121:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 2119b
	jmp 2115f
2114:
	mov rcx, QWORD PTR [rdi+248]
	shr rcx, 6
	mov rdx, r12
	sub rdx, 1
	cmp rcx, rdx
	jb 2125f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2127f
2129:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2129b
	jmp 2128f
2127:
2128:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
2130:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 2131f
	jmp 2132f
2131:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2133:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2134:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2135:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2135b
2132:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 2130b
	jmp 2126f
2125:
	mov edx, 1
	mov r8, QWORD PTR [rdi+112]
	mov eax, 0
	mov r14, 0
2136:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2136b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
2126:
2115:
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2137:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2137b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2138:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2139:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2139b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2140f
	mov r12, QWORD PTR [rdi+48]
	jmp 2141f
2140:
2141:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2142:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2142b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2143:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2143b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2144:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2144b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2145:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2145b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2138b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2146:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov rdi, QWORD PTR [rdi+128]
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2147:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2147b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+240]
	mov rsi, QWORD PTR [rax+112]
	mov r12, QWORD PTR [rax+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2148:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov edx, 1
	mov ecx, 1
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 5
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2149:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2150:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2151:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2151b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2152f
	mov r12, QWORD PTR [rdi+48]
	jmp 2153f
2152:
2153:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2154:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2154b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2155:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2155b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2156:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2156b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2157:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2150b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+200]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+160]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2158:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2158b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2159:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2160:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2160b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2161:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2162:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2161b
2163:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2164:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2165:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
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
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
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
2166:
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
	jne 2166b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 2165b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2164b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2163b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2167:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2167b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+72]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2168:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2169:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2170f
	mov r12, QWORD PTR [rdi+48]
	jmp 2171f
2170:
2171:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2172:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2172b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2173:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
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
	sbb rbp, rbp
	mov r14, 0
2175:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2175b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2168b
	mov r8, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov rsi, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov ebp, 0
	mov r14, 0
2176:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2176b
	mov r15, rbp
	mov ebp, 0
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2177:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2177b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2178:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2178b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+224]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2179:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2180f
	jmp 2181f
2180:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2181:
	test rdx, rdx
	jne 2179b
	mov r15, QWORD PTR [rdi+192]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2182:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov edx, 6
	mov ecx, 5
	mov r8d, 1
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
	jmp 260f
259:
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2183:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+96]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2184:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2185:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2185b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2186f
	mov r12, QWORD PTR [rdi+48]
	jmp 2187f
2186:
2187:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2188:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2188b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2189:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2189b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2190:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2190b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2191:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2191b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2184b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2192:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2192b
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2193:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2193b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+104]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2194:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2195:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2195b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2196f
	mov r12, QWORD PTR [rdi+48]
	jmp 2197f
2196:
2197:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2198:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2198b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2199:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2199b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2200:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2200b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2201:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2201b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2194b
	mov edx, 5
	mov ecx, 6
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2202:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2202b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2203:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2203b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+96]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2204:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2205:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2205b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2206f
	mov r12, QWORD PTR [rdi+48]
	jmp 2207f
2206:
2207:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2208:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2208b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2209:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2209b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
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
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2211:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2211b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2204b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2212:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2212b
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2213:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2213b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+104]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2214:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2215:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2215b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2216f
	mov r12, QWORD PTR [rdi+48]
	jmp 2217f
2216:
2217:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2218:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2218b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2219:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2219b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2220:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2220b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2221:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2221b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2214b
	mov edx, 5
	mov ecx, 6
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2222:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2222b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+48]
	xor rax, 32
	mov rdx, QWORD PTR [rdi+160]
	add rdx, 7
	shr rdx, 3
	xor rdx, 16
	or rax, rdx
	mov rdx, QWORD PTR [rdi+192]
	add rdx, 7
	shr rdx, 3
	xor rdx, 16
	or rax, rdx
	je 2223f
	mov rax, QWORD PTR [rdi+48]
	xor rax, 48
	mov rdx, QWORD PTR [rdi+160]
	add rdx, 7
	shr rdx, 3
	xor rdx, 24
	or rax, rdx
	mov rdx, QWORD PTR [rdi+192]
	add rdx, 7
	shr rdx, 3
	xor rdx, 24
	or rax, rdx
	je 2225f
	mov rdx, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [rdx+120]
	mov rdx, QWORD PTR [rdx+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov rdx, QWORD PTR [rdi+232]
	mov QWORD PTR [rdx+232], rax
	mov rdx, QWORD PTR [rdi+240]
	mov QWORD PTR [rdx+232], rax
	mov rdi, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2227:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2227b
	mov ecx, 64
	mov QWORD PTR [rdi+240], rcx
2228:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2229:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2229b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2230:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2230b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2231:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2231b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2228b
	mov r8d, 5
2232:
	cmp r8, 5
	je 2233f
	cmp r8, 4
	je 2235f
	cmp r8, 3
	je 2237f
	cmp r8, 2
	je 2239f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 12608
	movabs r12, 4503599627370495
	jmp 2240f
2239:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 352
	movabs r12, 4503599627370495
2240:
	jmp 2238f
2237:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 672
	movabs r12, 4503599627370495
2238:
	jmp 2236f
2235:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 12256
	movabs r12, 4503599627370495
2236:
	jmp 2234f
2233:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	movabs r12, 4503599627370495
2234:
	mov rax, QWORD PTR [rsi]
	and rax, r12
	mov QWORD PTR [r11], rax
	mov rax, QWORD PTR [rsi]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	mov rax, QWORD PTR [rsi+8]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsi+16]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	mov rax, QWORD PTR [rsi+24]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+32]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+160], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+40]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	and rax, r12
	mov QWORD PTR [r11+312], rax
	sub r8, 1
	jne 2232b
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+328], rax
	mov QWORD PTR [r11+336], rax
	mov QWORD PTR [r11+344], rax
	mov eax, 0
	mov QWORD PTR [r11+11552], rax
	mov QWORD PTR [r11+11560], rax
	mov QWORD PTR [r11+11568], rax
	mov QWORD PTR [r11+11576], rax
	mov QWORD PTR [r11+11584], rax
	mov QWORD PTR [r11+11592], rax
	mov QWORD PTR [r11+11600], rax
	mov QWORD PTR [r11+11608], rax
	mov QWORD PTR [r11+11616], rax
	mov QWORD PTR [r11+11624], rax
	mov QWORD PTR [r11+11632], rax
	mov QWORD PTR [r11+11640], rax
	mov QWORD PTR [r11+11648], rax
	mov QWORD PTR [r11+11656], rax
	mov QWORD PTR [r11+11664], rax
	mov QWORD PTR [r11+11672], rax
	mov QWORD PTR [r11+11680], rax
	mov QWORD PTR [r11+11688], rax
	mov QWORD PTR [r11+11696], rax
	mov QWORD PTR [r11+11704], rax
	mov QWORD PTR [r11+11712], rax
	mov QWORD PTR [r11+11720], rax
	mov QWORD PTR [r11+11728], rax
	mov QWORD PTR [r11+11736], rax
	mov QWORD PTR [r11+11744], rax
	mov QWORD PTR [r11+11752], rax
	mov QWORD PTR [r11+11760], rax
	mov QWORD PTR [r11+11768], rax
	mov QWORD PTR [r11+11776], rax
	mov QWORD PTR [r11+11784], rax
	mov QWORD PTR [r11+11792], rax
	mov QWORD PTR [r11+11800], rax
	mov QWORD PTR [r11+11808], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+200]
	mov rcx, QWORD PTR [rax+160]
	add r11, 11812
	sub r11, rcx
2241:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2241b
	mov r8, QWORD PTR [rdi+232]
	add r8, 11552
	mov r9, QWORD PTR [rdi+232]
	add r9, 11840
	mov ecx, 52
2242:
	mov eax, 0
	shl rax, 8
	movzx edx, BYTE PTR [r8]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+1]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+2]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+3]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+4]
	or rax, rdx
	mov rdx, rax
	shr rdx, 35
	and rdx, 31
	mov BYTE PTR [r9], dl
	mov rdx, rax
	shr rdx, 30
	and rdx, 31
	mov BYTE PTR [r9+1], dl
	mov rdx, rax
	shr rdx, 25
	and rdx, 31
	mov BYTE PTR [r9+2], dl
	mov rdx, rax
	shr rdx, 20
	and rdx, 31
	mov BYTE PTR [r9+3], dl
	mov rdx, rax
	shr rdx, 15
	and rdx, 31
	mov BYTE PTR [r9+4], dl
	mov rdx, rax
	shr rdx, 10
	and rdx, 31
	mov BYTE PTR [r9+5], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 31
	mov BYTE PTR [r9+6], dl
	mov rdx, rax
	and rdx, 31
	mov BYTE PTR [r9+7], dl
	add r8, 5
	add r9, 8
	sub rcx, 1
	jne 2242b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2243:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2243b
	mov ecx, 64
	mov QWORD PTR [rdi+240], rcx
2244:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2245:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2245b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2246:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2246b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2247:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2247b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2244b
	mov r8d, 5
2248:
	cmp r8, 5
	je 2249f
	cmp r8, 4
	je 2251f
	cmp r8, 3
	je 2253f
	cmp r8, 2
	je 2255f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 25536
	movabs r12, 4503599627370495
	jmp 2256f
2255:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 13280
	movabs r12, 4503599627370495
2256:
	jmp 2254f
2253:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 13600
	movabs r12, 4503599627370495
2254:
	jmp 2252f
2251:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 25184
	movabs r12, 4503599627370495
2252:
	jmp 2250f
2249:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 12928
	movabs r12, 4503599627370495
2250:
	mov rax, QWORD PTR [rsi]
	and rax, r12
	mov QWORD PTR [r11], rax
	mov rax, QWORD PTR [rsi]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	mov rax, QWORD PTR [rsi+8]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsi+16]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	mov rax, QWORD PTR [rsi+24]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+32]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+160], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+40]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	and rax, r12
	mov QWORD PTR [r11+312], rax
	sub r8, 1
	jne 2248b
	mov r11, QWORD PTR [rdi+232]
	add r11, 12928
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+328], rax
	mov QWORD PTR [r11+336], rax
	mov QWORD PTR [r11+344], rax
	mov eax, 0
	mov QWORD PTR [r11+11552], rax
	mov QWORD PTR [r11+11560], rax
	mov QWORD PTR [r11+11568], rax
	mov QWORD PTR [r11+11576], rax
	mov QWORD PTR [r11+11584], rax
	mov QWORD PTR [r11+11592], rax
	mov QWORD PTR [r11+11600], rax
	mov QWORD PTR [r11+11608], rax
	mov QWORD PTR [r11+11616], rax
	mov QWORD PTR [r11+11624], rax
	mov QWORD PTR [r11+11632], rax
	mov QWORD PTR [r11+11640], rax
	mov QWORD PTR [r11+11648], rax
	mov QWORD PTR [r11+11656], rax
	mov QWORD PTR [r11+11664], rax
	mov QWORD PTR [r11+11672], rax
	mov QWORD PTR [r11+11680], rax
	mov QWORD PTR [r11+11688], rax
	mov QWORD PTR [r11+11696], rax
	mov QWORD PTR [r11+11704], rax
	mov QWORD PTR [r11+11712], rax
	mov QWORD PTR [r11+11720], rax
	mov QWORD PTR [r11+11728], rax
	mov QWORD PTR [r11+11736], rax
	mov QWORD PTR [r11+11744], rax
	mov QWORD PTR [r11+11752], rax
	mov QWORD PTR [r11+11760], rax
	mov QWORD PTR [r11+11768], rax
	mov QWORD PTR [r11+11776], rax
	mov QWORD PTR [r11+11784], rax
	mov QWORD PTR [r11+11792], rax
	mov QWORD PTR [r11+11800], rax
	mov QWORD PTR [r11+11808], rax
	mov QWORD PTR [r11+12608], rax
	mov QWORD PTR [r11+12640], rax
	mov QWORD PTR [r11+12672], rax
	mov QWORD PTR [r11+12704], rax
	mov QWORD PTR [r11+12736], rax
	mov QWORD PTR [r11+12768], rax
	mov QWORD PTR [r11+12800], rax
	mov QWORD PTR [r11+12832], rax
	mov QWORD PTR [r11+12864], rax
	mov QWORD PTR [r11+12896], rax
	mov QWORD PTR [r11+12616], rax
	mov QWORD PTR [r11+12648], rax
	mov QWORD PTR [r11+12680], rax
	mov QWORD PTR [r11+12712], rax
	mov QWORD PTR [r11+12744], rax
	mov QWORD PTR [r11+12776], rax
	mov QWORD PTR [r11+12808], rax
	mov QWORD PTR [r11+12840], rax
	mov QWORD PTR [r11+12872], rax
	mov QWORD PTR [r11+12904], rax
	mov QWORD PTR [r11+12624], rax
	mov QWORD PTR [r11+12656], rax
	mov QWORD PTR [r11+12688], rax
	mov QWORD PTR [r11+12720], rax
	mov QWORD PTR [r11+12752], rax
	mov QWORD PTR [r11+12784], rax
	mov QWORD PTR [r11+12816], rax
	mov QWORD PTR [r11+12848], rax
	mov QWORD PTR [r11+12880], rax
	mov QWORD PTR [r11+12912], rax
	mov QWORD PTR [r11+12632], rax
	mov QWORD PTR [r11+12664], rax
	mov QWORD PTR [r11+12696], rax
	mov QWORD PTR [r11+12728], rax
	mov QWORD PTR [r11+12760], rax
	mov QWORD PTR [r11+12792], rax
	mov QWORD PTR [r11+12824], rax
	mov QWORD PTR [r11+12856], rax
	mov QWORD PTR [r11+12888], rax
	mov QWORD PTR [r11+12920], rax
	mov eax, 1
	mov QWORD PTR [r11+12608], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+216]
	mov rcx, QWORD PTR [rax+192]
	add r11, 11812
	sub r11, rcx
2257:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2257b
	mov r8, QWORD PTR [rdi+232]
	add r8, 24480
	mov r9, QWORD PTR [rdi+232]
	add r9, 24768
	mov ecx, 52
2258:
	mov eax, 0
	shl rax, 8
	movzx edx, BYTE PTR [r8]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+1]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+2]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+3]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+4]
	or rax, rdx
	mov rdx, rax
	shr rdx, 35
	and rdx, 31
	mov BYTE PTR [r9], dl
	mov rdx, rax
	shr rdx, 30
	and rdx, 31
	mov BYTE PTR [r9+1], dl
	mov rdx, rax
	shr rdx, 25
	and rdx, 31
	mov BYTE PTR [r9+2], dl
	mov rdx, rax
	shr rdx, 20
	and rdx, 31
	mov BYTE PTR [r9+3], dl
	mov rdx, rax
	shr rdx, 15
	and rdx, 31
	mov BYTE PTR [r9+4], dl
	mov rdx, rax
	shr rdx, 10
	and rdx, 31
	mov BYTE PTR [r9+5], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 31
	mov BYTE PTR [r9+6], dl
	mov rdx, rax
	and rdx, 31
	mov BYTE PTR [r9+7], dl
	add r8, 5
	add r9, 8
	sub rcx, 1
	jne 2258b
	mov rbx, QWORD PTR [rdi+232]
	stmxcsr DWORD PTR [rbx+25856]
	mov r11d, DWORD PTR [rbx+25856]
	and r11d, 65535
	mov DWORD PTR [rbx+25856], r11d
	mov eax, 8127
	mov DWORD PTR [rbx+25860], eax
	ldmxcsr DWORD PTR [rbx+25860]
	lfence
	mov r13d, 1312
2259:
	cmp r13, 1952
	jb 2260f
	mov r8, rbx
	add r8, r13
	sub r8, 320
	mov r9, rbx
	add r9, 672
	mov r11, rbx
	add r11, r13
	jmp 2261f
2260:
	mov r8, rbx
	add r8, r13
	sub r8, 960
	mov r9, rbx
	add r9, 12256
	mov r11, r8
2261:
	mov r10, rbx
	mov ecx, 4
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
	vpxorq ymm15, ymm15, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpxorq ymm19, ymm19, ymm19
	vpxorq ymm20, ymm20, ymm20
	vpxorq ymm21, ymm21, ymm21
	vpxorq ymm22, ymm22, ymm22
	vpxorq ymm23, ymm23, ymm23
	vpxorq ymm24, ymm24, ymm24
2262:
	mov rax, QWORD PTR [r9]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12928]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm10, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm0, 52
	vmovq xmm25, xmm25
	vpaddq ymm1, ymm1, ymm25
	valignq ymm0, ymm24, ymm0, 1
	vpsrlq ymm25, ymm10, 52
	vmovq xmm25, xmm25
	vpaddq ymm11, ymm11, ymm25
	valignq ymm10, ymm24, ymm10, 1
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12960]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm11, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm1, 52
	vmovq xmm25, xmm25
	vpaddq ymm2, ymm2, ymm25
	valignq ymm1, ymm24, ymm1, 1
	vpsrlq ymm25, ymm11, 52
	vmovq xmm25, xmm25
	vpaddq ymm12, ymm12, ymm25
	valignq ymm11, ymm24, ymm11, 1
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12992]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm12, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm2, 52
	vmovq xmm25, xmm25
	vpaddq ymm3, ymm3, ymm25
	valignq ymm2, ymm24, ymm2, 1
	vpsrlq ymm25, ymm12, 52
	vmovq xmm25, xmm25
	vpaddq ymm13, ymm13, ymm25
	valignq ymm12, ymm24, ymm12, 1
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13024]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm13, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm3, 52
	vmovq xmm25, xmm25
	vpaddq ymm4, ymm4, ymm25
	valignq ymm3, ymm24, ymm3, 1
	vpsrlq ymm25, ymm13, 52
	vmovq xmm25, xmm25
	vpaddq ymm14, ymm14, ymm25
	valignq ymm13, ymm24, ymm13, 1
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13056]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm14, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm4, 52
	vmovq xmm25, xmm25
	vpaddq ymm5, ymm5, ymm25
	valignq ymm4, ymm24, ymm4, 1
	vpsrlq ymm25, ymm14, 52
	vmovq xmm25, xmm25
	vpaddq ymm15, ymm15, ymm25
	valignq ymm14, ymm24, ymm14, 1
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13088]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm15, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm5, 52
	vmovq xmm25, xmm25
	vpaddq ymm6, ymm6, ymm25
	valignq ymm5, ymm24, ymm5, 1
	vpsrlq ymm25, ymm15, 52
	vmovq xmm25, xmm25
	vpaddq ymm16, ymm16, ymm25
	valignq ymm15, ymm24, ymm15, 1
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13120]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm16, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm6, 52
	vmovq xmm25, xmm25
	vpaddq ymm7, ymm7, ymm25
	valignq ymm6, ymm24, ymm6, 1
	vpsrlq ymm25, ymm16, 52
	vmovq xmm25, xmm25
	vpaddq ymm17, ymm17, ymm25
	valignq ymm16, ymm24, ymm16, 1
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13152]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm17, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm7, 52
	vmovq xmm25, xmm25
	vpaddq ymm8, ymm8, ymm25
	valignq ymm7, ymm24, ymm7, 1
	vpsrlq ymm25, ymm17, 52
	vmovq xmm25, xmm25
	vpaddq ymm18, ymm18, ymm25
	valignq ymm17, ymm24, ymm17, 1
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13184]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm8, 52
	vmovq xmm25, xmm25
	vpaddq ymm9, ymm9, ymm25
	valignq ymm8, ymm24, ymm8, 1
	vpsrlq ymm25, ymm18, 52
	vmovq xmm25, xmm25
	vpaddq ymm19, ymm19, ymm25
	valignq ymm18, ymm24, ymm18, 1
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13216]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm9, 52
	vmovq xmm25, xmm25
	vpaddq ymm0, ymm0, ymm25
	valignq ymm9, ymm24, ymm9, 1
	vpsrlq ymm25, ymm19, 52
	vmovq xmm25, xmm25
	vpaddq ymm10, ymm10, ymm25
	valignq ymm19, ymm24, ymm19, 1
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13216]
	add r9, 8
	sub rcx, 1
	jne 2262b
	vmovdqu64 YMMWORD PTR [r11], ymm0
	vmovdqu64 YMMWORD PTR [r11+32], ymm1
	vmovdqu64 YMMWORD PTR [r11+64], ymm2
	vmovdqu64 YMMWORD PTR [r11+96], ymm3
	vmovdqu64 YMMWORD PTR [r11+128], ymm4
	vmovdqu64 YMMWORD PTR [r11+160], ymm5
	vmovdqu64 YMMWORD PTR [r11+192], ymm6
	vmovdqu64 YMMWORD PTR [r11+224], ymm7
	vmovdqu64 YMMWORD PTR [r11+256], ymm8
	vmovdqu64 YMMWORD PTR [r11+288], ymm9
	vmovdqu64 YMMWORD PTR [r11+12928], ymm10
	vmovdqu64 YMMWORD PTR [r11+12960], ymm11
	vmovdqu64 YMMWORD PTR [r11+12992], ymm12
	vmovdqu64 YMMWORD PTR [r11+13024], ymm13
	vmovdqu64 YMMWORD PTR [r11+13056], ymm14
	vmovdqu64 YMMWORD PTR [r11+13088], ymm15
	vmovdqu64 YMMWORD PTR [r11+13120], ymm16
	vmovdqu64 YMMWORD PTR [r11+13152], ymm17
	vmovdqu64 YMMWORD PTR [r11+13184], ymm18
	vmovdqu64 YMMWORD PTR [r11+13216], ymm19
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12992]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12992], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13024]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13024], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13056]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13056], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13088]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13088], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13120]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13120], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13152]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13152], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+256]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13184]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13184], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+288]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13216]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13216], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13000]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13000], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13032]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13032], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13064]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13064], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13096]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13096], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13128]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13128], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13160]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13160], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+264]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13192]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13192], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+296]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13224]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13224], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13008]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13008], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13040]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13040], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13072]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13072], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13104]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13104], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13136]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13136], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13168]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13168], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+272]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13200]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13200], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+304]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13232]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13232], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12984], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13016]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13016], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13048]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13048], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13080]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13080], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13112]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13112], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13144]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13144], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13176]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13176], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+280]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13208]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13208], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+312]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13240]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13240], rcx
	shr rsi, 52
	cmp r13, 1632
	je 2263f
	jmp 2264f
2263:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+352]
	vmovdqu64 YMMWORD PTR [rbx+1312], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+384]
	vmovdqu64 YMMWORD PTR [rbx+1344], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+416]
	vmovdqu64 YMMWORD PTR [rbx+1376], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+448]
	vmovdqu64 YMMWORD PTR [rbx+1408], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+480]
	vmovdqu64 YMMWORD PTR [rbx+1440], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+512]
	vmovdqu64 YMMWORD PTR [rbx+1472], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+544]
	vmovdqu64 YMMWORD PTR [rbx+1504], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+576]
	vmovdqu64 YMMWORD PTR [rbx+1536], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+608]
	vmovdqu64 YMMWORD PTR [rbx+1568], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+640]
	vmovdqu64 YMMWORD PTR [rbx+1600], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13280]
	vmovdqu64 YMMWORD PTR [rbx+14240], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13312]
	vmovdqu64 YMMWORD PTR [rbx+14272], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13344]
	vmovdqu64 YMMWORD PTR [rbx+14304], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13376]
	vmovdqu64 YMMWORD PTR [rbx+14336], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13408]
	vmovdqu64 YMMWORD PTR [rbx+14368], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13440]
	vmovdqu64 YMMWORD PTR [rbx+14400], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13472]
	vmovdqu64 YMMWORD PTR [rbx+14432], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13504]
	vmovdqu64 YMMWORD PTR [rbx+14464], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13536]
	vmovdqu64 YMMWORD PTR [rbx+14496], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13568]
	vmovdqu64 YMMWORD PTR [rbx+14528], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+672]
	vmovdqu64 YMMWORD PTR [rbx+1632], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+704]
	vmovdqu64 YMMWORD PTR [rbx+1664], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+736]
	vmovdqu64 YMMWORD PTR [rbx+1696], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+768]
	vmovdqu64 YMMWORD PTR [rbx+1728], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+800]
	vmovdqu64 YMMWORD PTR [rbx+1760], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+832]
	vmovdqu64 YMMWORD PTR [rbx+1792], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+864]
	vmovdqu64 YMMWORD PTR [rbx+1824], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+896]
	vmovdqu64 YMMWORD PTR [rbx+1856], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+928]
	vmovdqu64 YMMWORD PTR [rbx+1888], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+960]
	vmovdqu64 YMMWORD PTR [rbx+1920], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13600]
	vmovdqu64 YMMWORD PTR [rbx+14560], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13632]
	vmovdqu64 YMMWORD PTR [rbx+14592], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13664]
	vmovdqu64 YMMWORD PTR [rbx+14624], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13696]
	vmovdqu64 YMMWORD PTR [rbx+14656], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13728]
	vmovdqu64 YMMWORD PTR [rbx+14688], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13760]
	vmovdqu64 YMMWORD PTR [rbx+14720], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13792]
	vmovdqu64 YMMWORD PTR [rbx+14752], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13824]
	vmovdqu64 YMMWORD PTR [rbx+14784], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13856]
	vmovdqu64 YMMWORD PTR [rbx+14816], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13888]
	vmovdqu64 YMMWORD PTR [rbx+14848], ymm0
2264:
	add r13, 320
	cmp r13, 11552
	jne 2259b
	mov r13d, 6
2265:
	cmp r13, 416
	je 2266f
	movzx eax, BYTE PTR [rbx+r13*1+11840]
	mov QWORD PTR [rbx+12576], rax
	movzx eax, BYTE PTR [rbx+r13*1+24768]
	mov QWORD PTR [rbx+25504], rax
	mov r8, rbx
	add r8, 1312
	mov rdx, QWORD PTR [rbx+12576]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
2268:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vmovdqu64 ymm11, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+256]
	vpternlogq ymm8, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+288]
	vpternlogq ymm9, ymm11, ymm10, 248
	add r8, 320
	add rcx, 1
	cmp rcx, 32
	jne 2268b
	vmovdqu64 YMMWORD PTR [rbx+992], ymm0
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm1
	vmovdqu64 YMMWORD PTR [rbx+1056], ymm2
	vmovdqu64 YMMWORD PTR [rbx+1088], ymm3
	vmovdqu64 YMMWORD PTR [rbx+1120], ymm4
	vmovdqu64 YMMWORD PTR [rbx+1152], ymm5
	vmovdqu64 YMMWORD PTR [rbx+1184], ymm6
	vmovdqu64 YMMWORD PTR [rbx+1216], ymm7
	vmovdqu64 YMMWORD PTR [rbx+1248], ymm8
	vmovdqu64 YMMWORD PTR [rbx+1280], ymm9
	mov r8, rbx
	add r8, 14240
	mov rdx, QWORD PTR [rbx+25504]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
2269:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vmovdqu64 ymm11, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+256]
	vpternlogq ymm8, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+288]
	vpternlogq ymm9, ymm11, ymm10, 248
	add r8, 320
	add rcx, 1
	cmp rcx, 32
	jne 2269b
	vmovdqu64 YMMWORD PTR [rbx+13920], ymm0
	vmovdqu64 YMMWORD PTR [rbx+13952], ymm1
	vmovdqu64 YMMWORD PTR [rbx+13984], ymm2
	vmovdqu64 YMMWORD PTR [rbx+14016], ymm3
	vmovdqu64 YMMWORD PTR [rbx+14048], ymm4
	vmovdqu64 YMMWORD PTR [rbx+14080], ymm5
	vmovdqu64 YMMWORD PTR [rbx+14112], ymm6
	vmovdqu64 YMMWORD PTR [rbx+14144], ymm7
	vmovdqu64 YMMWORD PTR [rbx+14176], ymm8
	vmovdqu64 YMMWORD PTR [rbx+14208], ymm9
	mov r15d, 6
	jmp 2267f
2266:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12608]
	vmovdqu64 YMMWORD PTR [rbx+992], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12640]
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12672]
	vmovdqu64 YMMWORD PTR [rbx+1056], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12704]
	vmovdqu64 YMMWORD PTR [rbx+1088], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12736]
	vmovdqu64 YMMWORD PTR [rbx+1120], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12768]
	vmovdqu64 YMMWORD PTR [rbx+1152], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12800]
	vmovdqu64 YMMWORD PTR [rbx+1184], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12832]
	vmovdqu64 YMMWORD PTR [rbx+1216], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12864]
	vmovdqu64 YMMWORD PTR [rbx+1248], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12896]
	vmovdqu64 YMMWORD PTR [rbx+1280], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25536]
	vmovdqu64 YMMWORD PTR [rbx+13920], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25568]
	vmovdqu64 YMMWORD PTR [rbx+13952], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25600]
	vmovdqu64 YMMWORD PTR [rbx+13984], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25632]
	vmovdqu64 YMMWORD PTR [rbx+14016], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25664]
	vmovdqu64 YMMWORD PTR [rbx+14048], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25696]
	vmovdqu64 YMMWORD PTR [rbx+14080], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25728]
	vmovdqu64 YMMWORD PTR [rbx+14112], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25760]
	vmovdqu64 YMMWORD PTR [rbx+14144], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25792]
	vmovdqu64 YMMWORD PTR [rbx+14176], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25824]
	vmovdqu64 YMMWORD PTR [rbx+14208], ymm0
	mov r15d, 1
2267:
2270:
	cmp r15, 1
	je 2271f
	mov r8, rbx
	add r8, 352
	mov r9, rbx
	add r9, 352
	mov r11, rbx
	add r11, 352
	jmp 2272f
2271:
	mov r8, rbx
	add r8, 352
	mov r9, rbx
	add r9, 992
	mov r11, rbx
	add r11, 352
2272:
	mov r10, rbx
	mov ecx, 4
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
	vpxorq ymm15, ymm15, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpxorq ymm19, ymm19, ymm19
	vpxorq ymm20, ymm20, ymm20
	vpxorq ymm21, ymm21, ymm21
	vpxorq ymm22, ymm22, ymm22
	vpxorq ymm23, ymm23, ymm23
	vpxorq ymm24, ymm24, ymm24
2273:
	mov rax, QWORD PTR [r9]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12928]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm10, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm0, 52
	vmovq xmm25, xmm25
	vpaddq ymm1, ymm1, ymm25
	valignq ymm0, ymm24, ymm0, 1
	vpsrlq ymm25, ymm10, 52
	vmovq xmm25, xmm25
	vpaddq ymm11, ymm11, ymm25
	valignq ymm10, ymm24, ymm10, 1
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12960]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm11, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm1, 52
	vmovq xmm25, xmm25
	vpaddq ymm2, ymm2, ymm25
	valignq ymm1, ymm24, ymm1, 1
	vpsrlq ymm25, ymm11, 52
	vmovq xmm25, xmm25
	vpaddq ymm12, ymm12, ymm25
	valignq ymm11, ymm24, ymm11, 1
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12992]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm12, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm2, 52
	vmovq xmm25, xmm25
	vpaddq ymm3, ymm3, ymm25
	valignq ymm2, ymm24, ymm2, 1
	vpsrlq ymm25, ymm12, 52
	vmovq xmm25, xmm25
	vpaddq ymm13, ymm13, ymm25
	valignq ymm12, ymm24, ymm12, 1
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13024]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm13, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm3, 52
	vmovq xmm25, xmm25
	vpaddq ymm4, ymm4, ymm25
	valignq ymm3, ymm24, ymm3, 1
	vpsrlq ymm25, ymm13, 52
	vmovq xmm25, xmm25
	vpaddq ymm14, ymm14, ymm25
	valignq ymm13, ymm24, ymm13, 1
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13056]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm14, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm4, 52
	vmovq xmm25, xmm25
	vpaddq ymm5, ymm5, ymm25
	valignq ymm4, ymm24, ymm4, 1
	vpsrlq ymm25, ymm14, 52
	vmovq xmm25, xmm25
	vpaddq ymm15, ymm15, ymm25
	valignq ymm14, ymm24, ymm14, 1
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13088]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm15, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm5, 52
	vmovq xmm25, xmm25
	vpaddq ymm6, ymm6, ymm25
	valignq ymm5, ymm24, ymm5, 1
	vpsrlq ymm25, ymm15, 52
	vmovq xmm25, xmm25
	vpaddq ymm16, ymm16, ymm25
	valignq ymm15, ymm24, ymm15, 1
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13120]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm16, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm6, 52
	vmovq xmm25, xmm25
	vpaddq ymm7, ymm7, ymm25
	valignq ymm6, ymm24, ymm6, 1
	vpsrlq ymm25, ymm16, 52
	vmovq xmm25, xmm25
	vpaddq ymm17, ymm17, ymm25
	valignq ymm16, ymm24, ymm16, 1
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13152]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm17, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm7, 52
	vmovq xmm25, xmm25
	vpaddq ymm8, ymm8, ymm25
	valignq ymm7, ymm24, ymm7, 1
	vpsrlq ymm25, ymm17, 52
	vmovq xmm25, xmm25
	vpaddq ymm18, ymm18, ymm25
	valignq ymm17, ymm24, ymm17, 1
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13184]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm8, 52
	vmovq xmm25, xmm25
	vpaddq ymm9, ymm9, ymm25
	valignq ymm8, ymm24, ymm8, 1
	vpsrlq ymm25, ymm18, 52
	vmovq xmm25, xmm25
	vpaddq ymm19, ymm19, ymm25
	valignq ymm18, ymm24, ymm18, 1
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13216]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm9, 52
	vmovq xmm25, xmm25
	vpaddq ymm0, ymm0, ymm25
	valignq ymm9, ymm24, ymm9, 1
	vpsrlq ymm25, ymm19, 52
	vmovq xmm25, xmm25
	vpaddq ymm10, ymm10, ymm25
	valignq ymm19, ymm24, ymm19, 1
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13216]
	add r9, 8
	sub rcx, 1
	jne 2273b
	vmovdqu64 YMMWORD PTR [r11], ymm0
	vmovdqu64 YMMWORD PTR [r11+32], ymm1
	vmovdqu64 YMMWORD PTR [r11+64], ymm2
	vmovdqu64 YMMWORD PTR [r11+96], ymm3
	vmovdqu64 YMMWORD PTR [r11+128], ymm4
	vmovdqu64 YMMWORD PTR [r11+160], ymm5
	vmovdqu64 YMMWORD PTR [r11+192], ymm6
	vmovdqu64 YMMWORD PTR [r11+224], ymm7
	vmovdqu64 YMMWORD PTR [r11+256], ymm8
	vmovdqu64 YMMWORD PTR [r11+288], ymm9
	vmovdqu64 YMMWORD PTR [r11+12928], ymm10
	vmovdqu64 YMMWORD PTR [r11+12960], ymm11
	vmovdqu64 YMMWORD PTR [r11+12992], ymm12
	vmovdqu64 YMMWORD PTR [r11+13024], ymm13
	vmovdqu64 YMMWORD PTR [r11+13056], ymm14
	vmovdqu64 YMMWORD PTR [r11+13088], ymm15
	vmovdqu64 YMMWORD PTR [r11+13120], ymm16
	vmovdqu64 YMMWORD PTR [r11+13152], ymm17
	vmovdqu64 YMMWORD PTR [r11+13184], ymm18
	vmovdqu64 YMMWORD PTR [r11+13216], ymm19
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12992]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12992], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13024]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13024], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13056]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13056], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13088]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13088], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13120]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13120], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13152]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13152], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+256]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13184]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13184], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+288]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13216]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13216], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13000]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13000], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13032]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13032], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13064]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13064], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13096]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13096], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13128]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13128], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13160]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13160], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+264]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13192]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13192], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+296]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13224]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13224], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13008]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13008], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13040]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13040], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13072]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13072], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13104]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13104], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13136]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13136], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13168]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13168], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+272]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13200]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13200], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+304]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13232]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13232], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12984], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13016]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13016], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13048]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13048], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13080]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13080], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13112]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13112], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13144]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13144], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13176]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13176], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+280]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13208]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13208], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+312]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13240]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13240], rcx
	shr rsi, 52
	sub r15, 1
	jne 2270b
	add r13, 1
	cmp r13, 417
	jne 2265b
	lfence
	ldmxcsr DWORD PTR [rbx+25856]
	vzeroupper
	mov r11, QWORD PTR [rdi+232]
	add r11, 13280
	mov r8, QWORD PTR [rdi+80]
	mov eax, 0
	mov rcx, QWORD PTR [r11]
	or rax, rcx
	mov rcx, QWORD PTR [r11+32]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+32]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+64]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+64]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+96]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+16], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+96]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+128]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+24], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+128]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+160]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+192]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+192]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+224]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+224]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+256]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+256]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+288]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+288]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+200]
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+232]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+264]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+264]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+296]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+176]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+240]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+272]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+272]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+304]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+304]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+200], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+88]
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+208], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+216], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+224], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+232], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+216]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+248]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+280]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+240], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+280]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+312]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+248], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+312]
	shr rcx, 20
	or rax, rcx
	mov QWORD PTR [r8+256], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
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
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2275:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2275b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rdi+232]
	add r11, 352
	mov r8, QWORD PTR [rdi+80]
	mov eax, 0
	mov rcx, QWORD PTR [r11]
	or rax, rcx
	mov rcx, QWORD PTR [r11+32]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+32]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+64]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+64]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+96]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+16], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+96]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+128]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+24], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+128]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+160]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+192]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+192]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+224]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+224]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+256]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+256]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+288]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+288]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+200]
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+232]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+264]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+264]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+296]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+176]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+240]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+272]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+272]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+304]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+304]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+200], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+88]
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+208], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+216], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+224], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+232], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+216]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+248]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+280]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+240], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+280]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+312]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+248], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+312]
	shr rcx, 20
	or rax, rcx
	mov QWORD PTR [r8+256], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2276:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2276b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2277:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2277b
	mov rdi, QWORD PTR [rdi+128]
	jmp 2226f
2225:
	mov rdx, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [rdx+120]
	mov rdx, QWORD PTR [rdx+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov rdx, QWORD PTR [rdi+232]
	mov QWORD PTR [rdx+232], rax
	mov rdx, QWORD PTR [rdi+240]
	mov QWORD PTR [rdx+232], rax
	mov rdi, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2278:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2278b
	mov ecx, 48
	mov QWORD PTR [rdi+240], rcx
2279:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2280:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2280b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2281:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2281b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2282:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2282b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2279b
	mov r8d, 5
2283:
	cmp r8, 5
	je 2284f
	cmp r8, 4
	je 2286f
	cmp r8, 3
	je 2288f
	cmp r8, 2
	je 2290f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10080
	movabs r12, 4503599627370495
	jmp 2291f
2290:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 288
	movabs r12, 4503599627370495
2291:
	jmp 2289f
2288:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 544
	movabs r12, 4503599627370495
2289:
	jmp 2287f
2286:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 9792
	movabs r12, 4503599627370495
2287:
	jmp 2285f
2284:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	movabs r12, 4503599627370495
2285:
	mov rax, QWORD PTR [rsi]
	and rax, r12
	mov QWORD PTR [r11], rax
	mov rax, QWORD PTR [rsi]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	mov rax, QWORD PTR [rsi+8]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsi+16]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	mov rax, QWORD PTR [rsi+24]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+32]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+160], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+40]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov eax, 0
	mov QWORD PTR [r11+216], rax
	mov eax, 0
	mov QWORD PTR [r11+248], rax
	sub r8, 1
	jne 2283b
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+256], rax
	mov QWORD PTR [r11+264], rax
	mov QWORD PTR [r11+272], rax
	mov QWORD PTR [r11+280], rax
	mov eax, 0
	mov QWORD PTR [r11+9248], rax
	mov QWORD PTR [r11+9256], rax
	mov QWORD PTR [r11+9264], rax
	mov QWORD PTR [r11+9272], rax
	mov QWORD PTR [r11+9280], rax
	mov QWORD PTR [r11+9288], rax
	mov QWORD PTR [r11+9296], rax
	mov QWORD PTR [r11+9304], rax
	mov QWORD PTR [r11+9312], rax
	mov QWORD PTR [r11+9320], rax
	mov QWORD PTR [r11+9328], rax
	mov QWORD PTR [r11+9336], rax
	mov QWORD PTR [r11+9344], rax
	mov QWORD PTR [r11+9352], rax
	mov QWORD PTR [r11+9360], rax
	mov QWORD PTR [r11+9368], rax
	mov QWORD PTR [r11+9376], rax
	mov QWORD PTR [r11+9384], rax
	mov QWORD PTR [r11+9392], rax
	mov QWORD PTR [r11+9400], rax
	mov QWORD PTR [r11+9408], rax
	mov QWORD PTR [r11+9416], rax
	mov QWORD PTR [r11+9424], rax
	mov QWORD PTR [r11+9432], rax
	mov QWORD PTR [r11+9440], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+200]
	mov rcx, QWORD PTR [rax+160]
	add r11, 9443
	sub r11, rcx
2292:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2292b
	mov r8, QWORD PTR [rdi+232]
	add r8, 9248
	mov r9, QWORD PTR [rdi+232]
	add r9, 9472
	mov ecx, 39
2293:
	mov eax, 0
	shl rax, 8
	movzx edx, BYTE PTR [r8]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+1]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+2]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+3]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+4]
	or rax, rdx
	mov rdx, rax
	shr rdx, 35
	and rdx, 31
	mov BYTE PTR [r9], dl
	mov rdx, rax
	shr rdx, 30
	and rdx, 31
	mov BYTE PTR [r9+1], dl
	mov rdx, rax
	shr rdx, 25
	and rdx, 31
	mov BYTE PTR [r9+2], dl
	mov rdx, rax
	shr rdx, 20
	and rdx, 31
	mov BYTE PTR [r9+3], dl
	mov rdx, rax
	shr rdx, 15
	and rdx, 31
	mov BYTE PTR [r9+4], dl
	mov rdx, rax
	shr rdx, 10
	and rdx, 31
	mov BYTE PTR [r9+5], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 31
	mov BYTE PTR [r9+6], dl
	mov rdx, rax
	and rdx, 31
	mov BYTE PTR [r9+7], dl
	add r8, 5
	add r9, 8
	sub rcx, 1
	jne 2293b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2294:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2294b
	mov ecx, 48
	mov QWORD PTR [rdi+240], rcx
2295:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2296:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2296b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2297:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2297b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2298:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2298b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2295b
	mov r8d, 5
2299:
	cmp r8, 5
	je 2300f
	cmp r8, 4
	je 2302f
	cmp r8, 3
	je 2304f
	cmp r8, 2
	je 2306f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 20416
	movabs r12, 4503599627370495
	jmp 2307f
2306:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10624
	movabs r12, 4503599627370495
2307:
	jmp 2305f
2304:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10880
	movabs r12, 4503599627370495
2305:
	jmp 2303f
2302:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 20128
	movabs r12, 4503599627370495
2303:
	jmp 2301f
2300:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10336
	movabs r12, 4503599627370495
2301:
	mov rax, QWORD PTR [rsi]
	and rax, r12
	mov QWORD PTR [r11], rax
	mov rax, QWORD PTR [rsi]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	mov rax, QWORD PTR [rsi+8]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsi+16]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	mov rax, QWORD PTR [rsi+24]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+32]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+160], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+40]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov eax, 0
	mov QWORD PTR [r11+216], rax
	mov eax, 0
	mov QWORD PTR [r11+248], rax
	sub r8, 1
	jne 2299b
	mov r11, QWORD PTR [rdi+232]
	add r11, 10336
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+256], rax
	mov QWORD PTR [r11+264], rax
	mov QWORD PTR [r11+272], rax
	mov QWORD PTR [r11+280], rax
	mov eax, 0
	mov QWORD PTR [r11+9248], rax
	mov QWORD PTR [r11+9256], rax
	mov QWORD PTR [r11+9264], rax
	mov QWORD PTR [r11+9272], rax
	mov QWORD PTR [r11+9280], rax
	mov QWORD PTR [r11+9288], rax
	mov QWORD PTR [r11+9296], rax
	mov QWORD PTR [r11+9304], rax
	mov QWORD PTR [r11+9312], rax
	mov QWORD PTR [r11+9320], rax
	mov QWORD PTR [r11+9328], rax
	mov QWORD PTR [r11+9336], rax
	mov QWORD PTR [r11+9344], rax
	mov QWORD PTR [r11+9352], rax
	mov QWORD PTR [r11+9360], rax
	mov QWORD PTR [r11+9368], rax
	mov QWORD PTR [r11+9376], rax
	mov QWORD PTR [r11+9384], rax
	mov QWORD PTR [r11+9392], rax
	mov QWORD PTR [r11+9400], rax
	mov QWORD PTR [r11+9408], rax
	mov QWORD PTR [r11+9416], rax
	mov QWORD PTR [r11+9424], rax
	mov QWORD PTR [r11+9432], rax
	mov QWORD PTR [r11+9440], rax
	mov QWORD PTR [r11+10080], rax
	mov QWORD PTR [r11+10112], rax
	mov QWORD PTR [r11+10144], rax
	mov QWORD PTR [r11+10176], rax
	mov QWORD PTR [r11+10208], rax
	mov QWORD PTR [r11+10240], rax
	mov QWORD PTR [r11+10272], rax
	mov QWORD PTR [r11+10304], rax
	mov QWORD PTR [r11+10088], rax
	mov QWORD PTR [r11+10120], rax
	mov QWORD PTR [r11+10152], rax
	mov QWORD PTR [r11+10184], rax
	mov QWORD PTR [r11+10216], rax
	mov QWORD PTR [r11+10248], rax
	mov QWORD PTR [r11+10280], rax
	mov QWORD PTR [r11+10312], rax
	mov QWORD PTR [r11+10096], rax
	mov QWORD PTR [r11+10128], rax
	mov QWORD PTR [r11+10160], rax
	mov QWORD PTR [r11+10192], rax
	mov QWORD PTR [r11+10224], rax
	mov QWORD PTR [r11+10256], rax
	mov QWORD PTR [r11+10288], rax
	mov QWORD PTR [r11+10320], rax
	mov QWORD PTR [r11+10104], rax
	mov QWORD PTR [r11+10136], rax
	mov QWORD PTR [r11+10168], rax
	mov QWORD PTR [r11+10200], rax
	mov QWORD PTR [r11+10232], rax
	mov QWORD PTR [r11+10264], rax
	mov QWORD PTR [r11+10296], rax
	mov QWORD PTR [r11+10328], rax
	mov eax, 1
	mov QWORD PTR [r11+10080], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+216]
	mov rcx, QWORD PTR [rax+192]
	add r11, 9443
	sub r11, rcx
2308:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2308b
	mov r8, QWORD PTR [rdi+232]
	add r8, 19584
	mov r9, QWORD PTR [rdi+232]
	add r9, 19808
	mov ecx, 39
2309:
	mov eax, 0
	shl rax, 8
	movzx edx, BYTE PTR [r8]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+1]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+2]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+3]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+4]
	or rax, rdx
	mov rdx, rax
	shr rdx, 35
	and rdx, 31
	mov BYTE PTR [r9], dl
	mov rdx, rax
	shr rdx, 30
	and rdx, 31
	mov BYTE PTR [r9+1], dl
	mov rdx, rax
	shr rdx, 25
	and rdx, 31
	mov BYTE PTR [r9+2], dl
	mov rdx, rax
	shr rdx, 20
	and rdx, 31
	mov BYTE PTR [r9+3], dl
	mov rdx, rax
	shr rdx, 15
	and rdx, 31
	mov BYTE PTR [r9+4], dl
	mov rdx, rax
	shr rdx, 10
	and rdx, 31
	mov BYTE PTR [r9+5], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 31
	mov BYTE PTR [r9+6], dl
	mov rdx, rax
	and rdx, 31
	mov BYTE PTR [r9+7], dl
	add r8, 5
	add r9, 8
	sub rcx, 1
	jne 2309b
	mov rbx, QWORD PTR [rdi+232]
	stmxcsr DWORD PTR [rbx+20672]
	mov r11d, DWORD PTR [rbx+20672]
	and r11d, 65535
	mov DWORD PTR [rbx+20672], r11d
	mov eax, 8127
	mov DWORD PTR [rbx+20676], eax
	ldmxcsr DWORD PTR [rbx+20676]
	lfence
	mov r13d, 1056
2310:
	cmp r13, 1568
	jb 2311f
	mov r8, rbx
	add r8, r13
	sub r8, 256
	mov r9, rbx
	add r9, 544
	mov r11, rbx
	add r11, r13
	jmp 2312f
2311:
	mov r8, rbx
	add r8, r13
	sub r8, 768
	mov r9, rbx
	add r9, 9792
	mov r11, r8
2312:
	mov r10, rbx
	mov ecx, 3
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
	vpxorq ymm15, ymm15, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpxorq ymm19, ymm19, ymm19
	vpxorq ymm20, ymm20, ymm20
2313:
	mov rax, QWORD PTR [r9]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10336]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm0, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm8, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm0, 52
	vmovq xmm21, xmm21
	vpaddq ymm1, ymm1, ymm21
	valignq ymm0, ymm20, ymm0, 1
	vpsrlq ymm21, ymm8, 52
	vmovq xmm21, xmm21
	vpaddq ymm9, ymm9, ymm21
	valignq ymm8, ymm20, ymm8, 1
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10368]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm1, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm9, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm1, 52
	vmovq xmm21, xmm21
	vpaddq ymm2, ymm2, ymm21
	valignq ymm1, ymm20, ymm1, 1
	vpsrlq ymm21, ymm9, 52
	vmovq xmm21, xmm21
	vpaddq ymm10, ymm10, ymm21
	valignq ymm9, ymm20, ymm9, 1
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10400]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm2, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm10, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm2, 52
	vmovq xmm21, xmm21
	vpaddq ymm3, ymm3, ymm21
	valignq ymm2, ymm20, ymm2, 1
	vpsrlq ymm21, ymm10, 52
	vmovq xmm21, xmm21
	vpaddq ymm11, ymm11, ymm21
	valignq ymm10, ymm20, ymm10, 1
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10432]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm3, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm11, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm3, 52
	vmovq xmm21, xmm21
	vpaddq ymm4, ymm4, ymm21
	valignq ymm3, ymm20, ymm3, 1
	vpsrlq ymm21, ymm11, 52
	vmovq xmm21, xmm21
	vpaddq ymm12, ymm12, ymm21
	valignq ymm11, ymm20, ymm11, 1
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10464]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm4, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm12, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm4, 52
	vmovq xmm21, xmm21
	vpaddq ymm5, ymm5, ymm21
	valignq ymm4, ymm20, ymm4, 1
	vpsrlq ymm21, ymm12, 52
	vmovq xmm21, xmm21
	vpaddq ymm13, ymm13, ymm21
	valignq ymm12, ymm20, ymm12, 1
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10496]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm5, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm13, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm5, 52
	vmovq xmm21, xmm21
	vpaddq ymm6, ymm6, ymm21
	valignq ymm5, ymm20, ymm5, 1
	vpsrlq ymm21, ymm13, 52
	vmovq xmm21, xmm21
	vpaddq ymm14, ymm14, ymm21
	valignq ymm13, ymm20, ymm13, 1
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10528]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm6, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm14, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm6, 52
	vmovq xmm21, xmm21
	vpaddq ymm7, ymm7, ymm21
	valignq ymm6, ymm20, ymm6, 1
	vpsrlq ymm21, ymm14, 52
	vmovq xmm21, xmm21
	vpaddq ymm15, ymm15, ymm21
	valignq ymm14, ymm20, ymm14, 1
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10560]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm7, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm15, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm7, 52
	vmovq xmm21, xmm21
	vpaddq ymm0, ymm0, ymm21
	valignq ymm7, ymm20, ymm7, 1
	vpsrlq ymm21, ymm15, 52
	vmovq xmm21, xmm21
	vpaddq ymm8, ymm8, ymm21
	valignq ymm15, ymm20, ymm15, 1
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10560]
	add r9, 8
	sub rcx, 1
	jne 2313b
	mov rax, QWORD PTR [r9]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10336]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm0, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm8, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm0, 52
	vmovq xmm21, xmm21
	vpaddq ymm1, ymm1, ymm21
	valignq ymm0, ymm20, ymm0, 1
	vpsrlq ymm21, ymm8, 52
	vmovq xmm21, xmm21
	vpaddq ymm9, ymm9, ymm21
	valignq ymm8, ymm20, ymm8, 1
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10368]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm1, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm9, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm1, 52
	vmovq xmm21, xmm21
	vpaddq ymm2, ymm2, ymm21
	valignq ymm1, ymm20, ymm1, 1
	vpsrlq ymm21, ymm9, 52
	vmovq xmm21, xmm21
	vpaddq ymm10, ymm10, ymm21
	valignq ymm9, ymm20, ymm9, 1
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10400]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm2, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm10, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm2, 52
	vmovq xmm21, xmm21
	vpaddq ymm3, ymm3, ymm21
	valignq ymm2, ymm20, ymm2, 1
	vpsrlq ymm21, ymm10, 52
	vmovq xmm21, xmm21
	vpaddq ymm11, ymm11, ymm21
	valignq ymm10, ymm20, ymm10, 1
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10432]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm3, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm11, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm3, 52
	vmovq xmm21, xmm21
	vpaddq ymm4, ymm4, ymm21
	valignq ymm3, ymm20, ymm3, 1
	vpsrlq ymm21, ymm11, 52
	vmovq xmm21, xmm21
	vpaddq ymm12, ymm12, ymm21
	valignq ymm11, ymm20, ymm11, 1
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10464]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm4, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm12, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm4, 52
	vmovq xmm21, xmm21
	vpaddq ymm5, ymm5, ymm21
	valignq ymm4, ymm20, ymm4, 1
	vpsrlq ymm21, ymm12, 52
	vmovq xmm21, xmm21
	vpaddq ymm13, ymm13, ymm21
	valignq ymm12, ymm20, ymm12, 1
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10496]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm5, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm13, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm5, 52
	vmovq xmm21, xmm21
	vpaddq ymm6, ymm6, ymm21
	valignq ymm5, ymm20, ymm5, 1
	vpsrlq ymm21, ymm13, 52
	vmovq xmm21, xmm21
	vpaddq ymm14, ymm14, ymm21
	valignq ymm13, ymm20, ymm13, 1
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10560]
	vmovdqu64 YMMWORD PTR [r11], ymm6
	vmovdqu64 YMMWORD PTR [r11+32], ymm7
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vmovdqu64 YMMWORD PTR [r11+192], ymm4
	vmovdqu64 YMMWORD PTR [r11+224], ymm5
	vmovdqu64 YMMWORD PTR [r11+10336], ymm14
	vmovdqu64 YMMWORD PTR [r11+10368], ymm15
	vmovdqu64 YMMWORD PTR [r11+10400], ymm8
	vmovdqu64 YMMWORD PTR [r11+10432], ymm9
	vmovdqu64 YMMWORD PTR [r11+10464], ymm10
	vmovdqu64 YMMWORD PTR [r11+10496], ymm11
	vmovdqu64 YMMWORD PTR [r11+10528], ymm12
	vmovdqu64 YMMWORD PTR [r11+10560], ymm13
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10336]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10336], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10368]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10368], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10400]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10400], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10432]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10432], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10464]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10464], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10496]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10496], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10528]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10528], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10560]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10560], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10344]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10344], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10376]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10376], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10408]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10408], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10440]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10440], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10472]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10472], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10504]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10504], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10536]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10536], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10568]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10568], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10352]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10352], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10384]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10384], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10416]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10416], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10448]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10448], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10480]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10480], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10512]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10512], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10544]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10544], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10576]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10576], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10360]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10360], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10392]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10392], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10424]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10424], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10456]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10456], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10488]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10488], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10520]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10520], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10552]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10552], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10584]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10584], rcx
	shr rsi, 52
	cmp r13, 1312
	je 2314f
	jmp 2315f
2314:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+288]
	vmovdqu64 YMMWORD PTR [rbx+1056], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+320]
	vmovdqu64 YMMWORD PTR [rbx+1088], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+352]
	vmovdqu64 YMMWORD PTR [rbx+1120], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+384]
	vmovdqu64 YMMWORD PTR [rbx+1152], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+416]
	vmovdqu64 YMMWORD PTR [rbx+1184], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+448]
	vmovdqu64 YMMWORD PTR [rbx+1216], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+480]
	vmovdqu64 YMMWORD PTR [rbx+1248], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+512]
	vmovdqu64 YMMWORD PTR [rbx+1280], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10624]
	vmovdqu64 YMMWORD PTR [rbx+11392], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10656]
	vmovdqu64 YMMWORD PTR [rbx+11424], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10688]
	vmovdqu64 YMMWORD PTR [rbx+11456], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10720]
	vmovdqu64 YMMWORD PTR [rbx+11488], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10752]
	vmovdqu64 YMMWORD PTR [rbx+11520], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10784]
	vmovdqu64 YMMWORD PTR [rbx+11552], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10816]
	vmovdqu64 YMMWORD PTR [rbx+11584], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10848]
	vmovdqu64 YMMWORD PTR [rbx+11616], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+544]
	vmovdqu64 YMMWORD PTR [rbx+1312], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+576]
	vmovdqu64 YMMWORD PTR [rbx+1344], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+608]
	vmovdqu64 YMMWORD PTR [rbx+1376], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+640]
	vmovdqu64 YMMWORD PTR [rbx+1408], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+672]
	vmovdqu64 YMMWORD PTR [rbx+1440], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+704]
	vmovdqu64 YMMWORD PTR [rbx+1472], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+736]
	vmovdqu64 YMMWORD PTR [rbx+1504], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+768]
	vmovdqu64 YMMWORD PTR [rbx+1536], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10880]
	vmovdqu64 YMMWORD PTR [rbx+11648], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10912]
	vmovdqu64 YMMWORD PTR [rbx+11680], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10944]
	vmovdqu64 YMMWORD PTR [rbx+11712], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10976]
	vmovdqu64 YMMWORD PTR [rbx+11744], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+11008]
	vmovdqu64 YMMWORD PTR [rbx+11776], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+11040]
	vmovdqu64 YMMWORD PTR [rbx+11808], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+11072]
	vmovdqu64 YMMWORD PTR [rbx+11840], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+11104]
	vmovdqu64 YMMWORD PTR [rbx+11872], ymm0
2315:
	add r13, 256
	cmp r13, 9248
	jne 2310b
	mov r13d, 4
2316:
	cmp r13, 312
	je 2317f
	movzx eax, BYTE PTR [rbx+r13*1+9472]
	mov QWORD PTR [rbx+10048], rax
	movzx eax, BYTE PTR [rbx+r13*1+19808]
	mov QWORD PTR [rbx+20384], rax
	mov r8, rbx
	add r8, 1056
	mov rdx, QWORD PTR [rbx+10048]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
2319:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm8, rax
	vpbroadcastq ymm8, xmm8
	vmovdqu64 ymm9, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm9, ymm8, 248
	add r8, 256
	add rcx, 1
	cmp rcx, 32
	jne 2319b
	vmovdqu64 YMMWORD PTR [rbx+800], ymm0
	vmovdqu64 YMMWORD PTR [rbx+832], ymm1
	vmovdqu64 YMMWORD PTR [rbx+864], ymm2
	vmovdqu64 YMMWORD PTR [rbx+896], ymm3
	vmovdqu64 YMMWORD PTR [rbx+928], ymm4
	vmovdqu64 YMMWORD PTR [rbx+960], ymm5
	vmovdqu64 YMMWORD PTR [rbx+992], ymm6
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm7
	mov r8, rbx
	add r8, 11392
	mov rdx, QWORD PTR [rbx+20384]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
2320:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm8, rax
	vpbroadcastq ymm8, xmm8
	vmovdqu64 ymm9, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm9, ymm8, 248
	add r8, 256
	add rcx, 1
	cmp rcx, 32
	jne 2320b
	vmovdqu64 YMMWORD PTR [rbx+11136], ymm0
	vmovdqu64 YMMWORD PTR [rbx+11168], ymm1
	vmovdqu64 YMMWORD PTR [rbx+11200], ymm2
	vmovdqu64 YMMWORD PTR [rbx+11232], ymm3
	vmovdqu64 YMMWORD PTR [rbx+11264], ymm4
	vmovdqu64 YMMWORD PTR [rbx+11296], ymm5
	vmovdqu64 YMMWORD PTR [rbx+11328], ymm6
	vmovdqu64 YMMWORD PTR [rbx+11360], ymm7
	mov r15d, 6
	jmp 2318f
2317:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10080]
	vmovdqu64 YMMWORD PTR [rbx+800], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10112]
	vmovdqu64 YMMWORD PTR [rbx+832], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10144]
	vmovdqu64 YMMWORD PTR [rbx+864], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10176]
	vmovdqu64 YMMWORD PTR [rbx+896], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10208]
	vmovdqu64 YMMWORD PTR [rbx+928], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10240]
	vmovdqu64 YMMWORD PTR [rbx+960], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10272]
	vmovdqu64 YMMWORD PTR [rbx+992], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10304]
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20416]
	vmovdqu64 YMMWORD PTR [rbx+11136], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20448]
	vmovdqu64 YMMWORD PTR [rbx+11168], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20480]
	vmovdqu64 YMMWORD PTR [rbx+11200], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20512]
	vmovdqu64 YMMWORD PTR [rbx+11232], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20544]
	vmovdqu64 YMMWORD PTR [rbx+11264], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20576]
	vmovdqu64 YMMWORD PTR [rbx+11296], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20608]
	vmovdqu64 YMMWORD PTR [rbx+11328], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20640]
	vmovdqu64 YMMWORD PTR [rbx+11360], ymm0
	mov r15d, 1
2318:
2321:
	cmp r15, 1
	je 2322f
	mov r8, rbx
	add r8, 288
	mov r9, rbx
	add r9, 288
	mov r11, rbx
	add r11, 288
	jmp 2323f
2322:
	mov r8, rbx
	add r8, 288
	mov r9, rbx
	add r9, 800
	mov r11, rbx
	add r11, 288
2323:
	mov r10, rbx
	mov ecx, 3
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
	vpxorq ymm15, ymm15, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpxorq ymm19, ymm19, ymm19
	vpxorq ymm20, ymm20, ymm20
2324:
	mov rax, QWORD PTR [r9]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10336]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm0, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm8, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm0, 52
	vmovq xmm21, xmm21
	vpaddq ymm1, ymm1, ymm21
	valignq ymm0, ymm20, ymm0, 1
	vpsrlq ymm21, ymm8, 52
	vmovq xmm21, xmm21
	vpaddq ymm9, ymm9, ymm21
	valignq ymm8, ymm20, ymm8, 1
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10368]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm1, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm9, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm1, 52
	vmovq xmm21, xmm21
	vpaddq ymm2, ymm2, ymm21
	valignq ymm1, ymm20, ymm1, 1
	vpsrlq ymm21, ymm9, 52
	vmovq xmm21, xmm21
	vpaddq ymm10, ymm10, ymm21
	valignq ymm9, ymm20, ymm9, 1
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10400]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm2, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm10, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm2, 52
	vmovq xmm21, xmm21
	vpaddq ymm3, ymm3, ymm21
	valignq ymm2, ymm20, ymm2, 1
	vpsrlq ymm21, ymm10, 52
	vmovq xmm21, xmm21
	vpaddq ymm11, ymm11, ymm21
	valignq ymm10, ymm20, ymm10, 1
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10432]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm3, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm11, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm3, 52
	vmovq xmm21, xmm21
	vpaddq ymm4, ymm4, ymm21
	valignq ymm3, ymm20, ymm3, 1
	vpsrlq ymm21, ymm11, 52
	vmovq xmm21, xmm21
	vpaddq ymm12, ymm12, ymm21
	valignq ymm11, ymm20, ymm11, 1
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10464]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm4, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm12, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm4, 52
	vmovq xmm21, xmm21
	vpaddq ymm5, ymm5, ymm21
	valignq ymm4, ymm20, ymm4, 1
	vpsrlq ymm21, ymm12, 52
	vmovq xmm21, xmm21
	vpaddq ymm13, ymm13, ymm21
	valignq ymm12, ymm20, ymm12, 1
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10496]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm5, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm13, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm5, 52
	vmovq xmm21, xmm21
	vpaddq ymm6, ymm6, ymm21
	valignq ymm5, ymm20, ymm5, 1
	vpsrlq ymm21, ymm13, 52
	vmovq xmm21, xmm21
	vpaddq ymm14, ymm14, ymm21
	valignq ymm13, ymm20, ymm13, 1
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10528]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm6, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm14, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm6, 52
	vmovq xmm21, xmm21
	vpaddq ymm7, ymm7, ymm21
	valignq ymm6, ymm20, ymm6, 1
	vpsrlq ymm21, ymm14, 52
	vmovq xmm21, xmm21
	vpaddq ymm15, ymm15, ymm21
	valignq ymm14, ymm20, ymm14, 1
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10560]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm7, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm15, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm7, 52
	vmovq xmm21, xmm21
	vpaddq ymm0, ymm0, ymm21
	valignq ymm7, ymm20, ymm7, 1
	vpsrlq ymm21, ymm15, 52
	vmovq xmm21, xmm21
	vpaddq ymm8, ymm8, ymm21
	valignq ymm15, ymm20, ymm15, 1
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10560]
	add r9, 8
	sub rcx, 1
	jne 2324b
	mov rax, QWORD PTR [r9]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10336]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm0, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm8, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm0, 52
	vmovq xmm21, xmm21
	vpaddq ymm1, ymm1, ymm21
	valignq ymm0, ymm20, ymm0, 1
	vpsrlq ymm21, ymm8, 52
	vmovq xmm21, xmm21
	vpaddq ymm9, ymm9, ymm21
	valignq ymm8, ymm20, ymm8, 1
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10368]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm1, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm9, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm1, 52
	vmovq xmm21, xmm21
	vpaddq ymm2, ymm2, ymm21
	valignq ymm1, ymm20, ymm1, 1
	vpsrlq ymm21, ymm9, 52
	vmovq xmm21, xmm21
	vpaddq ymm10, ymm10, ymm21
	valignq ymm9, ymm20, ymm9, 1
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10400]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm2, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm10, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm2, 52
	vmovq xmm21, xmm21
	vpaddq ymm3, ymm3, ymm21
	valignq ymm2, ymm20, ymm2, 1
	vpsrlq ymm21, ymm10, 52
	vmovq xmm21, xmm21
	vpaddq ymm11, ymm11, ymm21
	valignq ymm10, ymm20, ymm10, 1
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10432]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm3, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm11, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm3, 52
	vmovq xmm21, xmm21
	vpaddq ymm4, ymm4, ymm21
	valignq ymm3, ymm20, ymm3, 1
	vpsrlq ymm21, ymm11, 52
	vmovq xmm21, xmm21
	vpaddq ymm12, ymm12, ymm21
	valignq ymm11, ymm20, ymm11, 1
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10464]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm4, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm12, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm4, 52
	vmovq xmm21, xmm21
	vpaddq ymm5, ymm5, ymm21
	valignq ymm4, ymm20, ymm4, 1
	vpsrlq ymm21, ymm12, 52
	vmovq xmm21, xmm21
	vpaddq ymm13, ymm13, ymm21
	valignq ymm12, ymm20, ymm12, 1
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10496]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm5, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm13, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm5, 52
	vmovq xmm21, xmm21
	vpaddq ymm6, ymm6, ymm21
	valignq ymm5, ymm20, ymm5, 1
	vpsrlq ymm21, ymm13, 52
	vmovq xmm21, xmm21
	vpaddq ymm14, ymm14, ymm21
	valignq ymm13, ymm20, ymm13, 1
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10560]
	vmovdqu64 YMMWORD PTR [r11], ymm6
	vmovdqu64 YMMWORD PTR [r11+32], ymm7
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vmovdqu64 YMMWORD PTR [r11+192], ymm4
	vmovdqu64 YMMWORD PTR [r11+224], ymm5
	vmovdqu64 YMMWORD PTR [r11+10336], ymm14
	vmovdqu64 YMMWORD PTR [r11+10368], ymm15
	vmovdqu64 YMMWORD PTR [r11+10400], ymm8
	vmovdqu64 YMMWORD PTR [r11+10432], ymm9
	vmovdqu64 YMMWORD PTR [r11+10464], ymm10
	vmovdqu64 YMMWORD PTR [r11+10496], ymm11
	vmovdqu64 YMMWORD PTR [r11+10528], ymm12
	vmovdqu64 YMMWORD PTR [r11+10560], ymm13
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10336]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10336], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10368]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10368], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10400]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10400], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10432]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10432], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10464]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10464], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10496]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10496], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10528]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10528], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10560]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10560], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10344]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10344], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10376]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10376], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10408]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10408], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10440]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10440], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10472]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10472], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10504]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10504], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10536]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10536], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10568]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10568], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10352]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10352], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10384]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10384], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10416]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10416], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10448]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10448], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10480]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10480], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10512]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10512], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10544]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10544], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10576]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10576], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10360]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10360], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10392]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10392], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10424]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10424], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10456]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10456], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10488]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10488], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10520]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10520], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10552]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10552], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+10584]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+10584], rcx
	shr rsi, 52
	sub r15, 1
	jne 2321b
	add r13, 1
	cmp r13, 313
	jne 2316b
	lfence
	ldmxcsr DWORD PTR [rbx+20672]
	vzeroupper
	mov r11, QWORD PTR [rdi+232]
	add r11, 10624
	mov r8, QWORD PTR [rdi+80]
	mov eax, 0
	mov rcx, QWORD PTR [r11]
	or rax, rcx
	mov rcx, QWORD PTR [r11+32]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+32]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+64]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+64]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+96]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+16], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+96]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+128]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+24], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+128]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+160]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+192]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+192]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+224]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+224]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+8]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+168]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+200]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+200]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+208]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+240]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2325:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2325b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2326:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2326b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rdi+232]
	add r11, 288
	mov r8, QWORD PTR [rdi+80]
	mov eax, 0
	mov rcx, QWORD PTR [r11]
	or rax, rcx
	mov rcx, QWORD PTR [r11+32]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+32]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+64]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+64]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+96]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+16], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+96]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+128]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+24], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+128]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+160]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+192]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+192]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+224]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+224]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+8]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+168]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+200]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+200]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+208]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+240]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2327:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2327b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2328:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2328b
	mov rdi, QWORD PTR [rdi+128]
2226:
	jmp 2224f
2223:
	mov rdx, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [rdx+120]
	mov rdx, QWORD PTR [rdx+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov rdx, QWORD PTR [rdi+232]
	mov QWORD PTR [rdx+232], rax
	mov rdx, QWORD PTR [rdi+240]
	mov QWORD PTR [rdx+232], rax
	mov rdi, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2329:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2329b
	mov ecx, 32
	mov QWORD PTR [rdi+240], rcx
2330:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2331:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2331b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2332:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2332b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2333:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2333b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2330b
	mov r8d, 5
2334:
	cmp r8, 5
	je 2335f
	cmp r8, 4
	je 2337f
	cmp r8, 3
	je 2339f
	cmp r8, 2
	je 2341f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 3552
	movabs r12, 4503599627370495
	jmp 2342f
2341:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 192
	movabs r12, 4503599627370495
2342:
	jmp 2340f
2339:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 352
	movabs r12, 4503599627370495
2340:
	jmp 2338f
2337:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 3360
	movabs r12, 4503599627370495
2338:
	jmp 2336f
2335:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	movabs r12, 4503599627370495
2336:
	mov rax, QWORD PTR [rsi]
	and rax, r12
	mov QWORD PTR [r11], rax
	mov rax, QWORD PTR [rsi]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	mov rax, QWORD PTR [rsi+8]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsi+16]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	mov rax, QWORD PTR [rsi+24]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+32]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+40]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	and rax, r12
	mov QWORD PTR [r11+152], rax
	sub r8, 1
	jne 2334b
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+160], rax
	mov QWORD PTR [r11+168], rax
	mov QWORD PTR [r11+176], rax
	mov QWORD PTR [r11+184], rax
	mov eax, 0
	mov QWORD PTR [r11+3232], rax
	mov QWORD PTR [r11+3240], rax
	mov QWORD PTR [r11+3248], rax
	mov QWORD PTR [r11+3256], rax
	mov QWORD PTR [r11+3264], rax
	mov QWORD PTR [r11+3272], rax
	mov QWORD PTR [r11+3280], rax
	mov QWORD PTR [r11+3288], rax
	mov QWORD PTR [r11+3296], rax
	mov QWORD PTR [r11+3304], rax
	mov QWORD PTR [r11+3312], rax
	mov QWORD PTR [r11+3320], rax
	mov QWORD PTR [r11+3328], rax
	mov QWORD PTR [r11+3336], rax
	mov QWORD PTR [r11+3344], rax
	mov QWORD PTR [r11+3352], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+200]
	mov rcx, QWORD PTR [rax+160]
	add r11, 3360
	sub r11, rcx
2343:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2343b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2344:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2344b
	mov ecx, 32
	mov QWORD PTR [rdi+240], rcx
2345:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2346:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2346b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2347:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2347b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2348:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2348b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2345b
	mov r8d, 5
2349:
	cmp r8, 5
	je 2350f
	cmp r8, 4
	je 2352f
	cmp r8, 3
	je 2354f
	cmp r8, 2
	je 2356f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 7264
	movabs r12, 4503599627370495
	jmp 2357f
2356:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 3904
	movabs r12, 4503599627370495
2357:
	jmp 2355f
2354:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 4064
	movabs r12, 4503599627370495
2355:
	jmp 2353f
2352:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 7072
	movabs r12, 4503599627370495
2353:
	jmp 2351f
2350:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 3712
	movabs r12, 4503599627370495
2351:
	mov rax, QWORD PTR [rsi]
	and rax, r12
	mov QWORD PTR [r11], rax
	mov rax, QWORD PTR [rsi]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	mov rax, QWORD PTR [rsi+8]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsi+16]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	mov rax, QWORD PTR [rsi+24]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+32]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+40]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	and rax, r12
	mov QWORD PTR [r11+152], rax
	sub r8, 1
	jne 2349b
	mov r11, QWORD PTR [rdi+232]
	add r11, 3712
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+160], rax
	mov QWORD PTR [r11+168], rax
	mov QWORD PTR [r11+176], rax
	mov QWORD PTR [r11+184], rax
	mov eax, 0
	mov QWORD PTR [r11+3232], rax
	mov QWORD PTR [r11+3240], rax
	mov QWORD PTR [r11+3248], rax
	mov QWORD PTR [r11+3256], rax
	mov QWORD PTR [r11+3264], rax
	mov QWORD PTR [r11+3272], rax
	mov QWORD PTR [r11+3280], rax
	mov QWORD PTR [r11+3288], rax
	mov QWORD PTR [r11+3296], rax
	mov QWORD PTR [r11+3304], rax
	mov QWORD PTR [r11+3312], rax
	mov QWORD PTR [r11+3320], rax
	mov QWORD PTR [r11+3328], rax
	mov QWORD PTR [r11+3336], rax
	mov QWORD PTR [r11+3344], rax
	mov QWORD PTR [r11+3352], rax
	mov QWORD PTR [r11+3552], rax
	mov QWORD PTR [r11+3584], rax
	mov QWORD PTR [r11+3616], rax
	mov QWORD PTR [r11+3648], rax
	mov QWORD PTR [r11+3680], rax
	mov QWORD PTR [r11+3560], rax
	mov QWORD PTR [r11+3592], rax
	mov QWORD PTR [r11+3624], rax
	mov QWORD PTR [r11+3656], rax
	mov QWORD PTR [r11+3688], rax
	mov QWORD PTR [r11+3568], rax
	mov QWORD PTR [r11+3600], rax
	mov QWORD PTR [r11+3632], rax
	mov QWORD PTR [r11+3664], rax
	mov QWORD PTR [r11+3696], rax
	mov QWORD PTR [r11+3576], rax
	mov QWORD PTR [r11+3608], rax
	mov QWORD PTR [r11+3640], rax
	mov QWORD PTR [r11+3672], rax
	mov QWORD PTR [r11+3704], rax
	mov eax, 1
	mov QWORD PTR [r11+3552], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+216]
	mov rcx, QWORD PTR [rax+192]
	add r11, 3360
	sub r11, rcx
2358:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2358b
	mov rbx, QWORD PTR [rdi+232]
	stmxcsr DWORD PTR [rbx+7424]
	mov r11d, DWORD PTR [rbx+7424]
	and r11d, 65535
	mov DWORD PTR [rbx+7424], r11d
	mov eax, 8127
	mov DWORD PTR [rbx+7428], eax
	ldmxcsr DWORD PTR [rbx+7428]
	lfence
	mov r13d, 672
2359:
	cmp r13, 992
	jb 2360f
	mov r8, rbx
	add r8, r13
	sub r8, 160
	mov r9, rbx
	add r9, 352
	mov r11, rbx
	add r11, r13
	jmp 2361f
2360:
	mov r8, rbx
	add r8, r13
	sub r8, 480
	mov r9, rbx
	add r9, 3360
	mov r11, r8
2361:
	mov r10, rbx
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm26, ymm26, ymm26
	mov rax, QWORD PTR [r9]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8]
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	mov rax, QWORD PTR [r9+3712]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3712]
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm5, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm26, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3744]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm6, ymm6, ymm25
	vpaddq ymm6, ymm6, ymm23
	vpaddq ymm6, ymm6, ymm24
	vpsrlq ymm22, ymm5, 52
	vmovq xmm22, xmm22
	vpaddq ymm6, ymm6, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm6, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm5, ymm26, ymm5, 1
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm26, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3776]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm7, ymm7, ymm25
	vpaddq ymm7, ymm7, ymm23
	vpaddq ymm7, ymm7, ymm24
	vpsrlq ymm22, ymm6, 52
	vmovq xmm22, xmm22
	vpaddq ymm7, ymm7, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm7, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm6, ymm26, ymm6, 1
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm26, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3808]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm8, ymm8, ymm25
	vpaddq ymm8, ymm8, ymm23
	vpaddq ymm8, ymm8, ymm24
	vpsrlq ymm22, ymm7, 52
	vmovq xmm22, xmm22
	vpaddq ymm8, ymm8, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm8, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm7, ymm26, ymm7, 1
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm26, ymm3, 1
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3840]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm9, ymm9, ymm25
	vpaddq ymm9, ymm9, ymm23
	vpaddq ymm9, ymm9, ymm24
	vpsrlq ymm22, ymm8, 52
	vmovq xmm22, xmm22
	vpaddq ymm9, ymm9, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm9, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm8, ymm26, ymm8, 1
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+8]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm26, ymm4, 1
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3720]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm5, ymm5, ymm25
	vpaddq ymm5, ymm5, ymm23
	vpaddq ymm5, ymm5, ymm24
	vpsrlq ymm22, ymm9, 52
	vmovq xmm22, xmm22
	vpaddq ymm5, ymm5, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm5, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm9, ymm26, ymm9, 1
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+40]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm0, ymm26, ymm0, 1
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3752]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm6, ymm6, ymm25
	vpaddq ymm6, ymm6, ymm23
	vpaddq ymm6, ymm6, ymm24
	vpsrlq ymm22, ymm5, 52
	vmovq xmm22, xmm22
	vpaddq ymm6, ymm6, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm6, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm5, ymm26, ymm5, 1
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+72]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm1, ymm26, ymm1, 1
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3784]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm7, ymm7, ymm25
	vpaddq ymm7, ymm7, ymm23
	vpaddq ymm7, ymm7, ymm24
	vpsrlq ymm22, ymm6, 52
	vmovq xmm22, xmm22
	vpaddq ymm7, ymm7, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm7, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm6, ymm26, ymm6, 1
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+104]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm2, ymm26, ymm2, 1
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3816]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm8, ymm8, ymm25
	vpaddq ymm8, ymm8, ymm23
	vpaddq ymm8, ymm8, ymm24
	vpsrlq ymm22, ymm7, 52
	vmovq xmm22, xmm22
	vpaddq ymm8, ymm8, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm8, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm7, ymm26, ymm7, 1
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+136]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm3, ymm26, ymm3, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3848]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm9, ymm9, ymm25
	vpaddq ymm9, ymm9, ymm23
	vpaddq ymm9, ymm9, ymm24
	vpsrlq ymm22, ymm8, 52
	vmovq xmm22, xmm22
	vpaddq ymm9, ymm9, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm9, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm8, ymm26, ymm8, 1
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+16]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm4, ymm26, ymm4, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3728]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm5, ymm5, ymm25
	vpaddq ymm5, ymm5, ymm23
	vpaddq ymm5, ymm5, ymm24
	vpsrlq ymm22, ymm9, 52
	vmovq xmm22, xmm22
	vpaddq ymm5, ymm5, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm5, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm9, ymm26, ymm9, 1
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+48]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm26, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3760]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm6, ymm6, ymm25
	vpaddq ymm6, ymm6, ymm23
	vpaddq ymm6, ymm6, ymm24
	vpsrlq ymm22, ymm5, 52
	vmovq xmm22, xmm22
	vpaddq ymm6, ymm6, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm6, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm5, ymm26, ymm5, 1
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+80]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm26, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3792]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm7, ymm7, ymm25
	vpaddq ymm7, ymm7, ymm23
	vpaddq ymm7, ymm7, ymm24
	vpsrlq ymm22, ymm6, 52
	vmovq xmm22, xmm22
	vpaddq ymm7, ymm7, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm7, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm6, ymm26, ymm6, 1
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+112]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm26, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3824]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm8, ymm8, ymm25
	vpaddq ymm8, ymm8, ymm23
	vpaddq ymm8, ymm8, ymm24
	vpsrlq ymm22, ymm7, 52
	vmovq xmm22, xmm22
	vpaddq ymm8, ymm8, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm8, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm7, ymm26, ymm7, 1
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+144]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm26, ymm3, 1
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3856]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm9, ymm9, ymm25
	vpaddq ymm9, ymm9, ymm23
	vpaddq ymm9, ymm9, ymm24
	vpsrlq ymm22, ymm8, 52
	vmovq xmm22, xmm22
	vpaddq ymm9, ymm9, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm9, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm8, ymm26, ymm8, 1
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+24]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm26, ymm4, 1
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3736]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm5, ymm5, ymm25
	vpaddq ymm5, ymm5, ymm23
	vpaddq ymm5, ymm5, ymm24
	vpsrlq ymm22, ymm9, 52
	vmovq xmm22, xmm22
	vpaddq ymm5, ymm5, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm5, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm9, ymm26, ymm9, 1
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+56]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm0, ymm26, ymm0, 1
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3768]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm6, ymm6, ymm25
	vpaddq ymm6, ymm6, ymm23
	vpaddq ymm6, ymm6, ymm24
	vpsrlq ymm22, ymm5, 52
	vmovq xmm22, xmm22
	vpaddq ymm6, ymm6, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm6, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm5, ymm26, ymm5, 1
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+88]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm1, ymm26, ymm1, 1
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3800]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm7, ymm7, ymm25
	vpaddq ymm7, ymm7, ymm23
	vpaddq ymm7, ymm7, ymm24
	vpsrlq ymm22, ymm6, 52
	vmovq xmm22, xmm22
	vpaddq ymm7, ymm7, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm7, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm6, ymm26, ymm6, 1
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+120]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm2, ymm26, ymm2, 1
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3832]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm8, ymm8, ymm25
	vpaddq ymm8, ymm8, ymm23
	vpaddq ymm8, ymm8, ymm24
	vpsrlq ymm22, ymm7, 52
	vmovq xmm22, xmm22
	vpaddq ymm8, ymm8, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm8, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm7, ymm26, ymm7, 1
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+152]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm3, ymm26, ymm3, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3864]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm9, ymm9, ymm25
	vpaddq ymm9, ymm9, ymm23
	vpaddq ymm9, ymm9, ymm24
	vpsrlq ymm22, ymm8, 52
	vmovq xmm22, xmm22
	vpaddq ymm9, ymm9, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm9, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm8, ymm26, ymm8, 1
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	valignq ymm4, ymm26, ymm4, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm5, ymm5, ymm23
	vpaddq ymm5, ymm5, ymm24
	vpsrlq ymm22, ymm9, 52
	vmovq xmm22, xmm22
	vpaddq ymm5, ymm5, ymm22
	valignq ymm9, ymm26, ymm9, 1
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3840]
	vmovdqu64 YMMWORD PTR [r11], ymm0
	vmovdqu64 YMMWORD PTR [r11+32], ymm1
	vmovdqu64 YMMWORD PTR [r11+64], ymm2
	vmovdqu64 YMMWORD PTR [r11+96], ymm3
	vmovdqu64 YMMWORD PTR [r11+128], ymm4
	vmovdqu64 YMMWORD PTR [r11+3712], ymm5
	vmovdqu64 YMMWORD PTR [r11+3744], ymm6
	vmovdqu64 YMMWORD PTR [r11+3776], ymm7
	vmovdqu64 YMMWORD PTR [r11+3808], ymm8
	vmovdqu64 YMMWORD PTR [r11+3840], ymm9
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3712]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3712], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3744]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3744], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3776]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3776], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3720]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3720], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3752]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3752], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3784]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3784], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3728]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3728], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3760]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3760], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3792]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3792], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3736]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3736], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3768]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3768], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3864], rcx
	shr rsi, 52
	cmp r13, 832
	je 2362f
	jmp 2363f
2362:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+192]
	vmovdqu64 YMMWORD PTR [rbx+672], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+224]
	vmovdqu64 YMMWORD PTR [rbx+704], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+256]
	vmovdqu64 YMMWORD PTR [rbx+736], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+288]
	vmovdqu64 YMMWORD PTR [rbx+768], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+320]
	vmovdqu64 YMMWORD PTR [rbx+800], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+3904]
	vmovdqu64 YMMWORD PTR [rbx+4384], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+3936]
	vmovdqu64 YMMWORD PTR [rbx+4416], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+3968]
	vmovdqu64 YMMWORD PTR [rbx+4448], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4000]
	vmovdqu64 YMMWORD PTR [rbx+4480], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4032]
	vmovdqu64 YMMWORD PTR [rbx+4512], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+352]
	vmovdqu64 YMMWORD PTR [rbx+832], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+384]
	vmovdqu64 YMMWORD PTR [rbx+864], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+416]
	vmovdqu64 YMMWORD PTR [rbx+896], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+448]
	vmovdqu64 YMMWORD PTR [rbx+928], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+480]
	vmovdqu64 YMMWORD PTR [rbx+960], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4064]
	vmovdqu64 YMMWORD PTR [rbx+4544], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4096]
	vmovdqu64 YMMWORD PTR [rbx+4576], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4128]
	vmovdqu64 YMMWORD PTR [rbx+4608], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4160]
	vmovdqu64 YMMWORD PTR [rbx+4640], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4192]
	vmovdqu64 YMMWORD PTR [rbx+4672], ymm0
2363:
	add r13, 160
	cmp r13, 3232
	jne 2359b
	mov r13d, 0
2364:
	cmp r13, 256
	je 2365f
	mov r8, r13
	shr r8, 1
	mov rdx, r13
	and rdx, 1
	sub rdx, 1
	movzx eax, BYTE PTR [rbx+r8*1+3232]
	movzx esi, BYTE PTR [rbx+r8*1+6944]
	mov rcx, rax
	shr rcx, 4
	and rax, 15
	xor rcx, rax
	and rcx, rdx
	xor rax, rcx
	mov QWORD PTR [rbx+3520], rax
	mov rcx, rsi
	shr rcx, 4
	and rsi, 15
	xor rcx, rsi
	and rcx, rdx
	xor rsi, rcx
	mov QWORD PTR [rbx+7232], rsi
	mov r8, rbx
	add r8, 672
	mov rdx, QWORD PTR [rbx+3520]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
2367:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm5, rax
	vpbroadcastq ymm5, xmm5
	vmovdqu64 ymm6, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm6, ymm5, 248
	vmovdqu64 ymm6, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm6, ymm5, 248
	vmovdqu64 ymm6, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm6, ymm5, 248
	vmovdqu64 ymm6, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm6, ymm5, 248
	vmovdqu64 ymm6, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm6, ymm5, 248
	add r8, 160
	add rcx, 1
	cmp rcx, 16
	jne 2367b
	vmovdqu64 YMMWORD PTR [rbx+512], ymm0
	vmovdqu64 YMMWORD PTR [rbx+544], ymm1
	vmovdqu64 YMMWORD PTR [rbx+576], ymm2
	vmovdqu64 YMMWORD PTR [rbx+608], ymm3
	vmovdqu64 YMMWORD PTR [rbx+640], ymm4
	mov r8, rbx
	add r8, 4384
	mov rdx, QWORD PTR [rbx+7232]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
2368:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm5, rax
	vpbroadcastq ymm5, xmm5
	vmovdqu64 ymm6, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm6, ymm5, 248
	vmovdqu64 ymm6, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm6, ymm5, 248
	vmovdqu64 ymm6, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm6, ymm5, 248
	vmovdqu64 ymm6, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm6, ymm5, 248
	vmovdqu64 ymm6, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm6, ymm5, 248
	add r8, 160
	add rcx, 1
	cmp rcx, 16
	jne 2368b
	vmovdqu64 YMMWORD PTR [rbx+4224], ymm0
	vmovdqu64 YMMWORD PTR [rbx+4256], ymm1
	vmovdqu64 YMMWORD PTR [rbx+4288], ymm2
	vmovdqu64 YMMWORD PTR [rbx+4320], ymm3
	vmovdqu64 YMMWORD PTR [rbx+4352], ymm4
	mov r15d, 5
	jmp 2366f
2365:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+3552]
	vmovdqu64 YMMWORD PTR [rbx+512], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+3584]
	vmovdqu64 YMMWORD PTR [rbx+544], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+3616]
	vmovdqu64 YMMWORD PTR [rbx+576], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+3648]
	vmovdqu64 YMMWORD PTR [rbx+608], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+3680]
	vmovdqu64 YMMWORD PTR [rbx+640], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7264]
	vmovdqu64 YMMWORD PTR [rbx+4224], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7296]
	vmovdqu64 YMMWORD PTR [rbx+4256], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7328]
	vmovdqu64 YMMWORD PTR [rbx+4288], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7360]
	vmovdqu64 YMMWORD PTR [rbx+4320], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7392]
	vmovdqu64 YMMWORD PTR [rbx+4352], ymm0
	mov r15d, 1
2366:
2369:
	cmp r15, 1
	je 2370f
	mov r8, rbx
	add r8, 192
	mov r9, rbx
	add r9, 192
	mov r11, rbx
	add r11, 192
	jmp 2371f
2370:
	mov r8, rbx
	add r8, 192
	mov r9, rbx
	add r9, 512
	mov r11, rbx
	add r11, 192
2371:
	mov r10, rbx
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm26, ymm26, ymm26
	mov rax, QWORD PTR [r9]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8]
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	mov rax, QWORD PTR [r9+3712]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3712]
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm5, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm26, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3744]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm6, ymm6, ymm25
	vpaddq ymm6, ymm6, ymm23
	vpaddq ymm6, ymm6, ymm24
	vpsrlq ymm22, ymm5, 52
	vmovq xmm22, xmm22
	vpaddq ymm6, ymm6, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm6, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm5, ymm26, ymm5, 1
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm26, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3776]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm7, ymm7, ymm25
	vpaddq ymm7, ymm7, ymm23
	vpaddq ymm7, ymm7, ymm24
	vpsrlq ymm22, ymm6, 52
	vmovq xmm22, xmm22
	vpaddq ymm7, ymm7, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm7, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm6, ymm26, ymm6, 1
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm26, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3808]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm8, ymm8, ymm25
	vpaddq ymm8, ymm8, ymm23
	vpaddq ymm8, ymm8, ymm24
	vpsrlq ymm22, ymm7, 52
	vmovq xmm22, xmm22
	vpaddq ymm8, ymm8, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm8, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm7, ymm26, ymm7, 1
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm26, ymm3, 1
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3840]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm9, ymm9, ymm25
	vpaddq ymm9, ymm9, ymm23
	vpaddq ymm9, ymm9, ymm24
	vpsrlq ymm22, ymm8, 52
	vmovq xmm22, xmm22
	vpaddq ymm9, ymm9, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm9, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm8, ymm26, ymm8, 1
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+8]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm26, ymm4, 1
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3720]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm5, ymm5, ymm25
	vpaddq ymm5, ymm5, ymm23
	vpaddq ymm5, ymm5, ymm24
	vpsrlq ymm22, ymm9, 52
	vmovq xmm22, xmm22
	vpaddq ymm5, ymm5, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm5, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm9, ymm26, ymm9, 1
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+40]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm0, ymm26, ymm0, 1
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3752]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm6, ymm6, ymm25
	vpaddq ymm6, ymm6, ymm23
	vpaddq ymm6, ymm6, ymm24
	vpsrlq ymm22, ymm5, 52
	vmovq xmm22, xmm22
	vpaddq ymm6, ymm6, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm6, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm5, ymm26, ymm5, 1
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+72]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm1, ymm26, ymm1, 1
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3784]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm7, ymm7, ymm25
	vpaddq ymm7, ymm7, ymm23
	vpaddq ymm7, ymm7, ymm24
	vpsrlq ymm22, ymm6, 52
	vmovq xmm22, xmm22
	vpaddq ymm7, ymm7, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm7, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm6, ymm26, ymm6, 1
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+104]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm2, ymm26, ymm2, 1
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3816]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm8, ymm8, ymm25
	vpaddq ymm8, ymm8, ymm23
	vpaddq ymm8, ymm8, ymm24
	vpsrlq ymm22, ymm7, 52
	vmovq xmm22, xmm22
	vpaddq ymm8, ymm8, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm8, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm7, ymm26, ymm7, 1
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+136]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm3, ymm26, ymm3, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3848]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm9, ymm9, ymm25
	vpaddq ymm9, ymm9, ymm23
	vpaddq ymm9, ymm9, ymm24
	vpsrlq ymm22, ymm8, 52
	vmovq xmm22, xmm22
	vpaddq ymm9, ymm9, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm9, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm8, ymm26, ymm8, 1
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+16]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm4, ymm26, ymm4, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3728]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm5, ymm5, ymm25
	vpaddq ymm5, ymm5, ymm23
	vpaddq ymm5, ymm5, ymm24
	vpsrlq ymm22, ymm9, 52
	vmovq xmm22, xmm22
	vpaddq ymm5, ymm5, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm5, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm9, ymm26, ymm9, 1
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+48]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm26, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3760]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm6, ymm6, ymm25
	vpaddq ymm6, ymm6, ymm23
	vpaddq ymm6, ymm6, ymm24
	vpsrlq ymm22, ymm5, 52
	vmovq xmm22, xmm22
	vpaddq ymm6, ymm6, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm6, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm5, ymm26, ymm5, 1
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+80]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm26, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3792]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm7, ymm7, ymm25
	vpaddq ymm7, ymm7, ymm23
	vpaddq ymm7, ymm7, ymm24
	vpsrlq ymm22, ymm6, 52
	vmovq xmm22, xmm22
	vpaddq ymm7, ymm7, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm7, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm6, ymm26, ymm6, 1
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+112]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm26, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3824]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm8, ymm8, ymm25
	vpaddq ymm8, ymm8, ymm23
	vpaddq ymm8, ymm8, ymm24
	vpsrlq ymm22, ymm7, 52
	vmovq xmm22, xmm22
	vpaddq ymm8, ymm8, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm8, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm7, ymm26, ymm7, 1
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+144]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm26, ymm3, 1
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3856]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm9, ymm9, ymm25
	vpaddq ymm9, ymm9, ymm23
	vpaddq ymm9, ymm9, ymm24
	vpsrlq ymm22, ymm8, 52
	vmovq xmm22, xmm22
	vpaddq ymm9, ymm9, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm9, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm8, ymm26, ymm8, 1
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+24]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm26, ymm4, 1
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3736]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm5, ymm5, ymm25
	vpaddq ymm5, ymm5, ymm23
	vpaddq ymm5, ymm5, ymm24
	vpsrlq ymm22, ymm9, 52
	vmovq xmm22, xmm22
	vpaddq ymm5, ymm5, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm5, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm9, ymm26, ymm9, 1
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+56]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm0, ymm26, ymm0, 1
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3768]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm6, ymm6, ymm25
	vpaddq ymm6, ymm6, ymm23
	vpaddq ymm6, ymm6, ymm24
	vpsrlq ymm22, ymm5, 52
	vmovq xmm22, xmm22
	vpaddq ymm6, ymm6, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm6, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm5, ymm26, ymm5, 1
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+88]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm1, ymm26, ymm1, 1
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3800]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm7, ymm7, ymm25
	vpaddq ymm7, ymm7, ymm23
	vpaddq ymm7, ymm7, ymm24
	vpsrlq ymm22, ymm6, 52
	vmovq xmm22, xmm22
	vpaddq ymm7, ymm7, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm7, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm6, ymm26, ymm6, 1
	vpmadd52luq ymm8, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+120]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+160]
	vpbroadcastq ymm12, xmm14
	valignq ymm2, ymm26, ymm2, 1
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3832]
	vmovq xmm18, rax
	vpbroadcastq ymm18, xmm18
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r8+3712]
	vpaddq ymm8, ymm8, ymm25
	vpaddq ymm8, ymm8, ymm23
	vpaddq ymm8, ymm8, ymm24
	vpsrlq ymm22, ymm7, 52
	vmovq xmm22, xmm22
	vpaddq ymm8, ymm8, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm8, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm20, xmm22
	valignq ymm7, ymm26, ymm7, 1
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+152]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+160]
	vpbroadcastq ymm13, xmm14
	valignq ymm3, ymm26, ymm3, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm20, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm9, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm9, ymm18, YMMWORD PTR [r8+3712]
	mov rax, QWORD PTR [r9+3864]
	vmovq xmm19, rax
	vpbroadcastq ymm19, xmm19
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm9, ymm9, ymm25
	vpaddq ymm9, ymm9, ymm23
	vpaddq ymm9, ymm9, ymm24
	vpsrlq ymm22, ymm8, 52
	vmovq xmm22, xmm22
	vpaddq ymm9, ymm9, ymm22
	vpxorq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm9, YMMWORD PTR [r10+3872]
	vpbroadcastq ymm21, xmm22
	valignq ymm8, ymm26, ymm8, 1
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm8, ymm18, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r10+3840]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	valignq ymm4, ymm26, ymm4, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+3712]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm21, YMMWORD PTR [r10+3744]
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm21, YMMWORD PTR [r10+3712]
	vpmadd52luq ymm5, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52huq ymm5, ymm19, YMMWORD PTR [r8+3712]
	vpaddq ymm5, ymm5, ymm23
	vpaddq ymm5, ymm5, ymm24
	vpsrlq ymm22, ymm9, 52
	vmovq xmm22, xmm22
	vpaddq ymm5, ymm5, ymm22
	valignq ymm9, ymm26, ymm9, 1
	vpmadd52luq ymm6, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52huq ymm6, ymm19, YMMWORD PTR [r8+3744]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+3744]
	vpmadd52luq ymm7, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52huq ymm7, ymm19, YMMWORD PTR [r8+3776]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+3776]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r8+3808]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+3840]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+3808]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r8+3840]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+3840]
	vmovdqu64 YMMWORD PTR [r11], ymm0
	vmovdqu64 YMMWORD PTR [r11+32], ymm1
	vmovdqu64 YMMWORD PTR [r11+64], ymm2
	vmovdqu64 YMMWORD PTR [r11+96], ymm3
	vmovdqu64 YMMWORD PTR [r11+128], ymm4
	vmovdqu64 YMMWORD PTR [r11+3712], ymm5
	vmovdqu64 YMMWORD PTR [r11+3744], ymm6
	vmovdqu64 YMMWORD PTR [r11+3776], ymm7
	vmovdqu64 YMMWORD PTR [r11+3808], ymm8
	vmovdqu64 YMMWORD PTR [r11+3840], ymm9
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3712]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3712], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3744]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3744], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3776]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3776], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3720]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3720], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3752]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3752], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3784]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3784], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3728]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3728], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3760]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3760], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3792]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3792], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3736]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3736], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3768]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3768], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+3864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+3864], rcx
	shr rsi, 52
	sub r15, 1
	jne 2369b
	add r13, 1
	cmp r13, 257
	jne 2364b
	lfence
	ldmxcsr DWORD PTR [rbx+7424]
	vzeroupper
	mov r11, QWORD PTR [rdi+232]
	add r11, 3904
	mov r8, QWORD PTR [rdi+80]
	mov eax, 0
	mov rcx, QWORD PTR [r11]
	or rax, rcx
	mov rcx, QWORD PTR [r11+32]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+32]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+64]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+64]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+96]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+16], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+96]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+128]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+24], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+128]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+88]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 36
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2372:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2372b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2373:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2373b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rdi+232]
	add r11, 192
	mov r8, QWORD PTR [rdi+80]
	mov eax, 0
	mov rcx, QWORD PTR [r11]
	or rax, rcx
	mov rcx, QWORD PTR [r11+32]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+32]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+64]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+64]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+96]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+16], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+96]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+128]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+24], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+128]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+88]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 36
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2374:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2374b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2375:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2375b
	mov rdi, QWORD PTR [rdi+128]
2224:
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2376:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2376b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+96]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2377:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2378:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2378b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2379f
	mov r12, QWORD PTR [rdi+48]
	jmp 2380f
2379:
2380:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2381:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2381b
	mov rax, QWORD PTR [rdi+176]
	sub rax, r12
	mov QWORD PTR [rdi+176], rax
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], r12
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2382:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2382b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2383:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2383b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2384:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2384b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2377b
	mov rax, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rax+240]
	mov rsi, QWORD PTR [rax+112]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2385:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2385b
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2386:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2386b
	mov r8, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov rsi, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov ebp, 0
	mov r14, 0
2387:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2387b
	mov r15, rbp
	mov ebp, 0
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2388:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2388b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2389:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2389b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+224]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2390:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2391f
	jmp 2392f
2391:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2392:
	test rdx, rdx
	jne 2390b
	mov r15, QWORD PTR [rdi+192]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2393:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2393b
	mov edx, 6
	mov ecx, 5
	mov r8d, 1
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
260:
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2394:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2394b
	mov rax, QWORD PTR [rdi+240]
	mov rsi, QWORD PTR [rax+112]
	mov r12, QWORD PTR [rax+48]
	mov rbx, QWORD PTR [rdi+80]
	mov r14, 0
2395:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2395b
	mov rax, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rax+112]
	mov r10, QWORD PTR [rax+48]
	mov rax, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rax+64]
	mov r12, QWORD PTR [rax+48]
	mov r8, QWORD PTR [rdi+80]
	mov r13d, 0
2396:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2397:
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
	jne 2397b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 2396b
	mov rbx, QWORD PTR [rdi+80]
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2398:
	mov rbp, rdx
	and rbp, 7
	je 2399f
	jmp 2400f
2399:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2400:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2398b
	mov rax, QWORD PTR [rdi+176]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 21f
20:
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov eax, 0
2401:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2401b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
21:
	ret
	.p2align 6
