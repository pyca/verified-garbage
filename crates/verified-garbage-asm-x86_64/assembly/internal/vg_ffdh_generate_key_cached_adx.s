// The functions of `src/internal/vg_ffdh_generate_key_cached_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_generate_key_cached_adx:
	mov rax, QWORD PTR [rsp+32]
	mov r10, QWORD PTR [rsp+8]
	mov r11, QWORD PTR [rsp+16]
	mov QWORD PTR [rax], rbx
	mov QWORD PTR [rax+8], rbp
	mov QWORD PTR [rax+16], r12
	mov QWORD PTR [rax+24], r13
	mov QWORD PTR [rax+32], r14
	mov QWORD PTR [rax+40], r15
	mov QWORD PTR [rax+160], rdi
	mov QWORD PTR [rax+152], rdx
	mov QWORD PTR [rax+128], r8
	mov QWORD PTR [rax+136], r9
	mov QWORD PTR [rax+144], r10
	mov QWORD PTR [rax+200], r11
	mov rdi, rax
	mov rdx, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov rax, rdx
	add rax, rcx
	mov QWORD PTR [rdi+216], rax
	add rax, rcx
	mov QWORD PTR [rdi+224], rax
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
	mov rsi, QWORD PTR [rdi+152]
	mov rcx, QWORD PTR [rdi+144]
	mov eax, 0
22:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 22b
	mov rax, QWORD PTR [rsp+48]
	mov rsi, QWORD PTR [rax]
	mov rdx, QWORD PTR [rax+8]
	mov QWORD PTR [rdi+192], rdx
	shl rdx, 3
	sub rdx, rsi
	mov rcx, rdx
	mov eax, 255
	shr rax, cl
	mov QWORD PTR [rdi+248], rax
	mov r10, QWORD PTR [rdi+200]
	mov r11, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+248]
	mov r8, QWORD PTR [rdi+144]
	sub r8, QWORD PTR [rdi+192]
	mov ecx, 0
	mov r14, QWORD PTR [rdi+144]
23:
	movzx eax, BYTE PTR [r10]
	cmp rcx, r8
	mov edx, 255
	mov ebx, 0
	cmovb rdx, rbx
	cmove rdx, r9
	and rax, rdx
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	add rcx, 1
	sub r14, 1
	jne 23b
	mov rax, QWORD PTR [rdi+160]
	add rax, r8
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+168], rax
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
	mov rdx, rdi
	mov rax, QWORD PTR [rdx+120]
	mov rdx, QWORD PTR [rdx+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+232], rax
	mov r12, QWORD PTR [rdi+144]
	add r12, 7
	shr r12, 3
	cmp r12, 2
	jb 24f
	jmp 25f
24:
	mov r12d, 2
25:
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
26:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 26b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+144]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
27:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 28f
	jmp 29f
28:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
29:
	test rdx, rdx
	jne 27b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
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
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
210:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 210b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
211:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 211b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
212:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 213f
	jmp 214f
213:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
214:
	test rdx, rdx
	jne 212b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+120]
	mov ebp, 0
	mov r14, 0
215:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 215b
	mov rax, rbp
	and rax, 1
	xor rax, 1
	mov QWORD PTR [rdi+240], rax
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+136]
	sub rax, QWORD PTR [rdi+144]
	sub rax, QWORD PTR [rdi+144]
	je 216f
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+224]
	mov rcx, QWORD PTR [rax+144]
	mov rbx, QWORD PTR [rdi+112]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
222:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 222b
	mov rax, rbp
	and rax, 1
	jmp 217f
216:
	mov rdi, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+88]
	mov r14, 0
223:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 223b
	mov rbx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rbx]
	or rax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+88]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
224:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 224b
	mov rax, rbp
	and rax, 1
217:
	and rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	test rax, rax
	je 225f
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 227f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 229f
231:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 231b
	jmp 230f
229:
230:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
233:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
234:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 234b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
235:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 235b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
236:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 236b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 233b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
237:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 237b
	jmp 228f
227:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
238:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 238b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
239:
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
	jne 239b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
240:
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
241:
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
	jne 241b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
242:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
243:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 243b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 240b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
244:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 244b
228:
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+144], rdx
	mov QWORD PTR [rdi+168], rdx
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+160]
	mov QWORD PTR [rdi+184], rdx
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+168]
	mov QWORD PTR [rdi+192], rdx
245:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
246:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 246b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+184]
	mov r9, QWORD PTR [rdi+192]
	mov r13d, 0
	mov rax, QWORD PTR [rdi+168]
	sub rax, 1
	mov rdx, QWORD PTR [rdi+144]
	imul rdx, rdx, 0
	add rax, rdx
	mov rdx, r9
	shl rdx, 3
	cmp rax, rdx
	jb 247f
	mov edx, 0
	jmp 248f
247:
	mov r8, rax
	shr r8, 3
	mov r10, r9
	sub r10, r8
	movzx edx, BYTE PTR [rsi+r10*1-1]
	mov rcx, rax
	and rcx, 7
	shr rdx, cl
	and rdx, 1
248:
	or r13, rdx
	mov rax, QWORD PTR [rdi+168]
	sub rax, 1
	mov rdx, QWORD PTR [rdi+144]
	imul rdx, rdx, 1
	add rax, rdx
	mov rdx, r9
	shl rdx, 3
	cmp rax, rdx
	jb 249f
	mov edx, 0
	jmp 250f
249:
	mov r8, rax
	shr r8, 3
	mov r10, r9
	sub r10, r8
	movzx edx, BYTE PTR [rsi+r10*1-1]
	mov rcx, rax
	and rcx, 7
	shr rdx, cl
	and rdx, 1
250:
	shl rdx, 1
	or r13, rdx
	mov rax, QWORD PTR [rdi+168]
	sub rax, 1
	mov rdx, QWORD PTR [rdi+144]
	imul rdx, rdx, 2
	add rax, rdx
	mov rdx, r9
	shl rdx, 3
	cmp rax, rdx
	jb 251f
	mov edx, 0
	jmp 252f
251:
	mov r8, rax
	shr r8, 3
	mov r10, r9
	sub r10, r8
	movzx edx, BYTE PTR [rsi+r10*1-1]
	mov rcx, rax
	and rcx, 7
	shr rdx, cl
	and rdx, 1
252:
	shl rdx, 2
	or r13, rdx
	mov rax, QWORD PTR [rdi+168]
	sub rax, 1
	mov rdx, QWORD PTR [rdi+144]
	imul rdx, rdx, 3
	add rax, rdx
	mov rdx, r9
	shl rdx, 3
	cmp rax, rdx
	jb 253f
	mov edx, 0
	jmp 254f
253:
	mov r8, rax
	shr r8, 3
	mov r10, r9
	sub r10, r8
	movzx edx, BYTE PTR [rsi+r10*1-1]
	mov rcx, rax
	and rcx, 7
	shr rdx, cl
	and rdx, 1
254:
	shl rdx, 3
	or r13, rdx
	mov rax, QWORD PTR [rdi+168]
	sub rax, 1
	mov rdx, QWORD PTR [rdi+144]
	imul rdx, rdx, 4
	add rax, rdx
	mov rdx, r9
	shl rdx, 3
	cmp rax, rdx
	jb 255f
	mov edx, 0
	jmp 256f
255:
	mov r8, rax
	shr r8, 3
	mov r10, r9
	sub r10, r8
	movzx edx, BYTE PTR [rsi+r10*1-1]
	mov rcx, rax
	and rcx, 7
	shr rdx, cl
	and rdx, 1
256:
	shl rdx, 4
	or r13, rdx
	mov eax, 0
	mov QWORD PTR [rdi+176], rax
257:
	mov rax, QWORD PTR [rdi+176]
	xor rax, r13
	cmp rax, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+176]
	add rax, 2
	mov r12, QWORD PTR [rdi+48]
	mov rbx, rax
	imul rbx, r12
	shl rbx, 3
	add rbx, QWORD PTR [rdi+136]
	add rbx, 24
	mov rsi, rbx
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
258:
	mov rax, QWORD PTR [rsi+r14*8]
	and rax, rdx
	or rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
	mov rax, QWORD PTR [rdi+176]
	add rax, 1
	mov QWORD PTR [rdi+176], rax
	cmp rax, 32
	jne 257b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+168]
	sub rax, 1
	mov QWORD PTR [rdi+168], rax
	jne 245b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rax+176], rdx
	mov rdx, QWORD PTR [rax+216]
	mov QWORD PTR [rax+152], rdx
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+120]
	mov r10, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
259:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rax, rbp
	and rax, 1
	mov QWORD PTR [rdi+240], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+88]
	mov r14, 0
260:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov rbx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rbx]
	or rax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+88]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
261:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 261b
	mov rax, rbp
	and rax, 1
	and rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov r15d, 0
	sub r15, rax
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+176]
	mov rcx, QWORD PTR [rax+144]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
262:
	mov rbp, rdx
	and rbp, 7
	je 263f
	jmp 264f
263:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
264:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 262b
	mov rax, QWORD PTR [rdi+240]
	mov rdi, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+240], rax
	mov r15d, 0
	sub r15, rax
	mov r11, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+144]
	sub rdx, QWORD PTR [rdi+168]
	sub r11, rdx
	mov rcx, QWORD PTR [rdi+144]
265:
	movzx eax, BYTE PTR [r11]
	and rax, r15
	mov BYTE PTR [r11], al
	add r11, 1
	sub rcx, 1
	jne 265b
	mov rax, QWORD PTR [rdi+240]
	shl rax, 1
	mov edx, 3
	sub rdx, rax
	mov rax, rdx
	jmp 226f
225:
	mov rdi, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+240], rax
	mov r15d, 0
	sub r15, rax
	mov r11, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+144]
	sub rdx, QWORD PTR [rdi+168]
	sub r11, rdx
	mov rcx, QWORD PTR [rdi+144]
266:
	movzx eax, BYTE PTR [r11]
	and rax, r15
	mov BYTE PTR [r11], al
	add r11, 1
	sub rcx, 1
	jne 266b
	mov eax, 2
226:
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
