// The functions of `src/internal/vg_rsa_private_crt_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_crt_adx:
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
	mov rax, QWORD PTR [r10+r12*8-16]
	mul rcx
	mov r9, rax
	mov r11, rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	mul rcx
	add rax, r11
	adc rdx, 0
	mov r13, QWORD PTR [rbx+r12*8-24]
	sub r13, r9
	mov r14, QWORD PTR [rbx+r12*8-16]
	sbb r14, rax
	mov r15, QWORD PTR [rbx+r12*8-8]
	sbb r15, rdx
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov r11, r15
	add r11, r11
	sbb r11, r11
	add rcx, r11
	mov rax, QWORD PTR [r10+r12*8-16]
	and rax, r11
	mov rdx, QWORD PTR [r10+r12*8-8]
	and rdx, r11
	add r13, rax
	adc r14, rdx
	adc r15, 0
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
	mov rsi, r8
	mov r14, 0
226:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 223b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
227:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 227b
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
	jb 228f
	jmp 229f
228:
	mov r12d, 2
229:
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
	jb 230f
	jmp 231f
230:
	mov r12d, 2
231:
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
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+152]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
233:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 234f
	jmp 235f
234:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
235:
	test rdx, rdx
	jne 233b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
236:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 236b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+224]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
237:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 238f
	jmp 239f
238:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
239:
	test rdx, rdx
	jne 237b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
240:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 240b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+184]
	mov rcx, QWORD PTR [rax+192]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
241:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 242f
	jmp 243f
242:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
243:
	test rdx, rdx
	jne 241b
	mov rdi, QWORD PTR [rdi+128]
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
244:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 244b
	mov rax, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rax+64]
	mov r10, QWORD PTR [rax+48]
	mov rax, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rax+64]
	mov r12, QWORD PTR [rax+48]
	mov r8, QWORD PTR [rdi+80]
	mov r13d, 0
245:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
246:
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
	jne 246b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 245b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+80]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
247:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 247b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	add r12, 2
	mov r14, 0
248:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 248b
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
249:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 249b
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
250:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
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
251:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
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
252:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 252b
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
253:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 253b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [rax+48]
	mov r12, QWORD PTR [rdi+48]
	mov ecx, 0
254:
	add rcx, rax
	cmp rcx, r12
	jb 254b
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
	jne 255f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 257f
259:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 259b
	jmp 258f
257:
258:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
260:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 261f
	jmp 262f
261:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
263:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 263b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
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
262:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 260b
	jmp 256f
255:
	mov rcx, QWORD PTR [rdi+248]
	shr rcx, 6
	mov rdx, r12
	sub rdx, 1
	cmp rcx, rdx
	jb 266f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 268f
270:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 270b
	jmp 269f
268:
269:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
271:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 272f
	jmp 273f
272:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
274:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 274b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
275:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 275b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
276:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 276b
273:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 271b
	jmp 267f
266:
	mov edx, 1
	mov r8, QWORD PTR [rdi+112]
	mov eax, 0
	mov r14, 0
277:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
267:
256:
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
278:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 278b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
279:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
280:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 280b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 281f
	mov r12, QWORD PTR [rdi+48]
	jmp 282f
281:
282:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
283:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
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
284:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 284b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
285:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 285b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
286:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 286b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 279b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
287:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 287b
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
288:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 288b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
289:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
290:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 290b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 291f
	mov r12, QWORD PTR [rdi+48]
	jmp 292f
291:
292:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
293:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 293b
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
294:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 294b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
295:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 295b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
296:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 289b
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
297:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
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
298:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 298b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
299:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 299b
	mov eax, 30
	mov QWORD PTR [rdi+160], rax
2100:
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
2101:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2101b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2100b
	mov rcx, QWORD PTR [rdi+144]
	movabs rax, -3689348814741910323
	mul rcx
	shr rdx, 2
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rdx
	sub rcx, rax
	add rcx, rcx
	mov rax, rcx
	sub rax, 5
	cmovb rax, rcx
	mov QWORD PTR [rdi+160], rax
	mov ecx, 0
	mov QWORD PTR [rdi+168], rcx
	movabs rcx, 72057594037927936
	mov rdx, rcx
	shr rdx, 1
	cmp rax, 1
	cmovae rcx, rdx
	mov rdx, rcx
	shr rdx, 1
	cmp rax, 2
	cmovae rcx, rdx
	mov rdx, rcx
	shr rdx, 1
	cmp rax, 3
	cmovae rcx, rdx
	mov rdx, rcx
	shr rdx, 1
	cmp rax, 4
	cmovae rcx, rdx
	mov QWORD PTR [rdi+232], rcx
2102:
	mov rax, QWORD PTR [rdi+160]
	cmp rax, 5
	jb 2103f
	jmp 2104f
2103:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+160]
	movzx eax, BYTE PTR [rax+rcx*1]
	imul rax, rdx
	or rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	add rcx, 1
	mov QWORD PTR [rdi+152], rcx
	shr rdx, 8
	mov QWORD PTR [rdi+232], rdx
	add r8, 8
	mov QWORD PTR [rdi+160], r8
2104:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rax, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+232]
	mov rcx, QWORD PTR [rdi+160]
	shl rdx, 5
	mov QWORD PTR [rdi+232], rdx
	sub rcx, 5
	mov QWORD PTR [rdi+160], rcx
	mov rdx, rax
	shr rdx, 59
	mov QWORD PTR [rdi+216], rdx
	shl rax, 5
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2105:
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
	mov r12, r13
	shr r12, 2
	add r12, r12
	add r12, r12
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm8, r14
	vpbroadcastq ymm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm9, r14
	vpbroadcastq ymm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm10, r14
	vpbroadcastq ymm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm11, r14
	vpbroadcastq ymm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm12, r14
	vpbroadcastq ymm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm13, r14
	vpbroadcastq ymm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm14, r14
	vpbroadcastq ymm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm15, r14
	vpbroadcastq ymm15, xmm15
	mov r14d, 0
	cmp r14, r15
	sbb r14, r14
	vmovq xmm7, r14
	vpbroadcastq ymm7, xmm7
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
	test r12, r12
	jne 2106f
	jmp 2107f
2106:
2108:
	vpand ymm0, ymm8, YMMWORD PTR [rcx+r14*8]
	vpand ymm1, ymm9, YMMWORD PTR [rdx+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm10, YMMWORD PTR [rsi+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm11, YMMWORD PTR [rbp+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm12, YMMWORD PTR [r8+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm13, YMMWORD PTR [r9+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm14, YMMWORD PTR [r10+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm15, YMMWORD PTR [rax+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm7, YMMWORD PTR [rbx+r14*8]
	vpor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+r14*8], ymm0
	add r14, 4
	cmp r14, r12
	jne 2108b
2107:
	cmp r14, r13
	jne 2109f
	jmp 2110f
2109:
	vpand xmm0, xmm8, XMMWORD PTR [rcx+r14*8]
	vpand xmm1, xmm9, XMMWORD PTR [rdx+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm10, XMMWORD PTR [rsi+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm11, XMMWORD PTR [rbp+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm12, XMMWORD PTR [r8+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm13, XMMWORD PTR [r9+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm14, XMMWORD PTR [r10+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm15, XMMWORD PTR [rax+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm7, XMMWORD PTR [rbx+r14*8]
	vpor xmm0, xmm0, xmm1
	vmovdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
2110:
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 32
	jne 2105b
	vzeroupper
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+144]
	sub rax, QWORD PTR [rdi+152]
	add rax, QWORD PTR [rdi+160]
	jne 2102b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+232]
	mov rax, QWORD PTR [rax+48]
	mov r12, QWORD PTR [rdi+48]
	mov ecx, 0
2111:
	add rcx, rax
	cmp rcx, r12
	jb 2111b
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
	jne 2112f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2114f
2116:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2116b
	jmp 2115f
2114:
2115:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
2117:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 2118f
	jmp 2119f
2118:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2120:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2121:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2122:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2122b
2119:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 2117b
	jmp 2113f
2112:
	mov rcx, QWORD PTR [rdi+248]
	shr rcx, 6
	mov rdx, r12
	sub rdx, 1
	cmp rcx, rdx
	jb 2123f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2125f
2127:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2127b
	jmp 2126f
2125:
2126:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
2128:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 2129f
	jmp 2130f
2129:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2131:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2131b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2132:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2132b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2133:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2133b
2130:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 2128b
	jmp 2124f
2123:
	mov edx, 1
	mov r8, QWORD PTR [rdi+112]
	mov eax, 0
	mov r14, 0
2134:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
2124:
2113:
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2135:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2135b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2136:
	mov r8, QWORD PTR [rdi+72]
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
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2138f
	mov r12, QWORD PTR [rdi+48]
	jmp 2139f
2138:
2139:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2140:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2140b
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
2141:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2141b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2142:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2142b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2143:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2143b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2136b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2144:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	mov rdi, QWORD PTR [rdi+128]
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2145:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2145b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+240]
	mov rsi, QWORD PTR [rax+112]
	mov r12, QWORD PTR [rax+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2146:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
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
2147:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2147b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2148:
	mov r8, QWORD PTR [rdi+72]
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
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2150f
	mov r12, QWORD PTR [rdi+48]
	jmp 2151f
2150:
2151:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2152:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
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
2153:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2153b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2154:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2154b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2155:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2155b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2148b
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
2156:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
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
2157:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2158:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2158b
	mov eax, 30
	mov QWORD PTR [rdi+160], rax
2159:
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
2160:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2160b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2159b
	mov rcx, QWORD PTR [rdi+144]
	movabs rax, -3689348814741910323
	mul rcx
	shr rdx, 2
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rdx
	sub rcx, rax
	add rcx, rcx
	mov rax, rcx
	sub rax, 5
	cmovb rax, rcx
	mov QWORD PTR [rdi+160], rax
	mov ecx, 0
	mov QWORD PTR [rdi+168], rcx
	movabs rcx, 72057594037927936
	mov rdx, rcx
	shr rdx, 1
	cmp rax, 1
	cmovae rcx, rdx
	mov rdx, rcx
	shr rdx, 1
	cmp rax, 2
	cmovae rcx, rdx
	mov rdx, rcx
	shr rdx, 1
	cmp rax, 3
	cmovae rcx, rdx
	mov rdx, rcx
	shr rdx, 1
	cmp rax, 4
	cmovae rcx, rdx
	mov QWORD PTR [rdi+232], rcx
2161:
	mov rax, QWORD PTR [rdi+160]
	cmp rax, 5
	jb 2162f
	jmp 2163f
2162:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+160]
	movzx eax, BYTE PTR [rax+rcx*1]
	imul rax, rdx
	or rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	add rcx, 1
	mov QWORD PTR [rdi+152], rcx
	shr rdx, 8
	mov QWORD PTR [rdi+232], rdx
	add r8, 8
	mov QWORD PTR [rdi+160], r8
2163:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rax, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+232]
	mov rcx, QWORD PTR [rdi+160]
	shl rdx, 5
	mov QWORD PTR [rdi+232], rdx
	sub rcx, 5
	mov QWORD PTR [rdi+160], rcx
	mov rdx, rax
	shr rdx, 59
	mov QWORD PTR [rdi+216], rdx
	shl rax, 5
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2164:
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
	mov r12, r13
	shr r12, 2
	add r12, r12
	add r12, r12
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm8, r14
	vpbroadcastq ymm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm9, r14
	vpbroadcastq ymm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm10, r14
	vpbroadcastq ymm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm11, r14
	vpbroadcastq ymm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm12, r14
	vpbroadcastq ymm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm13, r14
	vpbroadcastq ymm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm14, r14
	vpbroadcastq ymm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	vmovq xmm15, r14
	vpbroadcastq ymm15, xmm15
	mov r14d, 0
	cmp r14, r15
	sbb r14, r14
	vmovq xmm7, r14
	vpbroadcastq ymm7, xmm7
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
	test r12, r12
	jne 2165f
	jmp 2166f
2165:
2167:
	vpand ymm0, ymm8, YMMWORD PTR [rcx+r14*8]
	vpand ymm1, ymm9, YMMWORD PTR [rdx+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm10, YMMWORD PTR [rsi+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm11, YMMWORD PTR [rbp+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm12, YMMWORD PTR [r8+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm13, YMMWORD PTR [r9+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm14, YMMWORD PTR [r10+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm15, YMMWORD PTR [rax+r14*8]
	vpor ymm0, ymm0, ymm1
	vpand ymm1, ymm7, YMMWORD PTR [rbx+r14*8]
	vpor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+r14*8], ymm0
	add r14, 4
	cmp r14, r12
	jne 2167b
2166:
	cmp r14, r13
	jne 2168f
	jmp 2169f
2168:
	vpand xmm0, xmm8, XMMWORD PTR [rcx+r14*8]
	vpand xmm1, xmm9, XMMWORD PTR [rdx+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm10, XMMWORD PTR [rsi+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm11, XMMWORD PTR [rbp+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm12, XMMWORD PTR [r8+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm13, XMMWORD PTR [r9+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm14, XMMWORD PTR [r10+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm15, XMMWORD PTR [rax+r14*8]
	vpor xmm0, xmm0, xmm1
	vpand xmm1, xmm7, XMMWORD PTR [rbx+r14*8]
	vpor xmm0, xmm0, xmm1
	vmovdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
2169:
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 32
	jne 2164b
	vzeroupper
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+144]
	sub rax, QWORD PTR [rdi+152]
	add rax, QWORD PTR [rdi+160]
	jne 2161b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2170:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2170b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+72]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2171:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2172:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2172b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2173f
	mov r12, QWORD PTR [rdi+48]
	jmp 2174f
2173:
2174:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2175:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2175b
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
2176:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2176b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2177:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2177b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2178:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2178b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2171b
	mov r8, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov rsi, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov ebp, 0
	mov r14, 0
2179:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2179b
	mov r15, rbp
	mov ebp, 0
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2180:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2180b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2181:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+224]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2182:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2183f
	jmp 2184f
2183:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2184:
	test rdx, rdx
	jne 2182b
	mov r15, QWORD PTR [rdi+192]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2185:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2185b
	mov edx, 6
	mov ecx, 5
	mov r8d, 1
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2186:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2186b
	mov rax, QWORD PTR [rdi+240]
	mov rsi, QWORD PTR [rax+112]
	mov r12, QWORD PTR [rax+48]
	mov rbx, QWORD PTR [rdi+80]
	mov r14, 0
2187:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2187b
	mov rax, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rax+112]
	mov r10, QWORD PTR [rax+48]
	mov rax, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rax+64]
	mov r12, QWORD PTR [rax+48]
	mov r8, QWORD PTR [rdi+80]
	mov r13d, 0
2188:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2189:
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
	jne 2189b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 2188b
	mov rbx, QWORD PTR [rdi+80]
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2190:
	mov rbp, rdx
	and rbp, 7
	je 2191f
	jmp 2192f
2191:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2192:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2190b
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
2193:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2193b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
21:
	ret
	.p2align 6
