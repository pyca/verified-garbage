// The functions of `src/internal/vg_rsa_public_precomputed_checked.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precomputed_checked:
	mov r11d, 0
	mov r10d, 0
20:
	ror r11, 56
	movzx eax, BYTE PTR [r8+r10*1]
	add r11, rax
	mov rax, r11
	shr rax, 33
	cmp rax, 1
	sbb rax, rax
	and r11, rax
	xor rax, -1
	shr rax, 30
	or r11, rax
	add r10, 1
	cmp r10, r9
	jne 20b
	mov rax, r11
	shr rax, 33
	mov r10, r11
	and r10, 1
	xor r10, 1
	or rax, r10
	cmp r11, 3
	sbb r10, r10
	or rax, r10
	test rax, rax
	jne 21f
	mov r11, QWORD PTR [rsp+24]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov QWORD PTR [r11+128], rdi
	mov QWORD PTR [r11+136], rdx
	mov QWORD PTR [r11+144], rsi
	mov QWORD PTR [r11+152], r8
	mov QWORD PTR [r11+160], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+168], rax
	mov rdi, r11
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
	mov r14, 0
23:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 23b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rsi, rax
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
24:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 24b
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov rax, r12
	and rax, 7
	cmp rax, 0
	je 25f
	mov r14, 0
27:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 27b
	jmp 26f
25:
	mov r14d, 0
28:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov rax, QWORD PTR [rbx+r14*8+8]
	sbb rax, QWORD PTR [r10+r14*8+8]
	mov rax, QWORD PTR [rbx+r14*8+16]
	sbb rax, QWORD PTR [r10+r14*8+16]
	mov rax, QWORD PTR [rbx+r14*8+24]
	sbb rax, QWORD PTR [r10+r14*8+24]
	mov rax, QWORD PTR [rbx+r14*8+32]
	sbb rax, QWORD PTR [r10+r14*8+32]
	mov rax, QWORD PTR [rbx+r14*8+40]
	sbb rax, QWORD PTR [r10+r14*8+40]
	mov rax, QWORD PTR [rbx+r14*8+48]
	sbb rax, QWORD PTR [r10+r14*8+48]
	mov rax, QWORD PTR [rbx+r14*8+56]
	sbb rax, QWORD PTR [r10+r14*8+56]
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 28b
26:
	mov rax, QWORD PTR [r10]
	and rax, 1
	and rax, rbp
	mov rdx, QWORD PTR [r10+r12*8-8]
	cmp rdx, 1
	sbb rdx, rdx
	add rdx, 1
	and rax, rdx
	test rax, rax
	je 29f
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+144]
	mov rbx, QWORD PTR [rdi+72]
	mov rax, rcx
	and rax, 7
	cmp rax, 0
	je 211f
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
213:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 214f
	jmp 215f
214:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
215:
	test rdx, rdx
	jne 213b
	jmp 212f
211:
	mov r14, rsi
	add r14, rcx
	mov edx, 0
216:
	sub r14, 8
	mov rax, QWORD PTR [r14]
	bswap rax
	mov QWORD PTR [rbx+rdx*1], rax
	add rdx, 8
	cmp rdx, rcx
	jne 216b
212:
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov rax, r12
	and rax, 7
	cmp rax, 0
	je 217f
	mov r14, 0
219:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 219b
	jmp 218f
217:
	mov r14d, 0
220:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov rax, QWORD PTR [rbx+r14*8+8]
	sbb rax, QWORD PTR [r10+r14*8+8]
	mov rax, QWORD PTR [rbx+r14*8+16]
	sbb rax, QWORD PTR [r10+r14*8+16]
	mov rax, QWORD PTR [rbx+r14*8+24]
	sbb rax, QWORD PTR [r10+r14*8+24]
	mov rax, QWORD PTR [rbx+r14*8+32]
	sbb rax, QWORD PTR [r10+r14*8+32]
	mov rax, QWORD PTR [rbx+r14*8+40]
	sbb rax, QWORD PTR [r10+r14*8+40]
	mov rax, QWORD PTR [rbx+r14*8+48]
	sbb rax, QWORD PTR [r10+r14*8+48]
	mov rax, QWORD PTR [rbx+r14*8+56]
	sbb rax, QWORD PTR [r10+r14*8+56]
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 220b
218:
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
221:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 221b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rbx, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+72]
	mov r9, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
223:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
224:
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
	jne 224b
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
225:
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
	jne 225b
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
	jne 223b
	mov ebp, 0
	mov r14, 0
226:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 226b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
227:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 227b
	mov r8, QWORD PTR [rdi+152]
	mov r9, QWORD PTR [rdi+160]
	mov r11d, 0
	mov r10d, 0
228:
	ror r11, 56
	movzx eax, BYTE PTR [r8+r10*1]
	add r11, rax
	mov rax, r11
	shr rax, 33
	cmp rax, 1
	sbb rax, rax
	and r11, rax
	xor rax, -1
	shr rax, 30
	or r11, rax
	add r10, 1
	cmp r10, r9
	jne 228b
	mov rax, r11
	shr rax, 33
	mov r10, r11
	and r10, 1
	xor r10, 1
	or rax, r10
	cmp r11, 3
	sbb r10, r10
	or rax, r10
	test rax, rax
	cmp r11, 65537
	je 229f
	mov eax, 0
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+216], rax
231:
	mov rax, QWORD PTR [rdi+152]
	mov rcx, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rax+rcx*1]
	add rcx, 1
	sub rcx, QWORD PTR [rdi+160]
	cmp rcx, 1
	sbb rcx, rcx
	sub rcx, 1
	and rax, rcx
	mov QWORD PTR [rdi+200], rax
	mov eax, 8
	mov QWORD PTR [rdi+192], rax
232:
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	jne 233f
	jmp 234f
233:
	mov rbx, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	mov eax, 0
	mov r14, 0
235:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 235b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
236:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
237:
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
	jne 237b
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
238:
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
	jne 238b
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
	jne 236b
	mov ebp, 0
	mov r14, 0
239:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 239b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
240:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 240b
234:
	mov rax, QWORD PTR [rdi+200]
	shr rax, 7
	and rax, 1
	jne 241f
	jmp 242f
241:
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	jne 243f
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
245:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 245b
	mov eax, 1
	mov QWORD PTR [rdi+216], rax
	jmp 244f
243:
	mov rbx, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	mov eax, 0
	mov r14, 0
246:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 246b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
247:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
248:
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
	jne 248b
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
249:
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
	jne 249b
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
	jne 247b
	mov ebp, 0
	mov r14, 0
250:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 250b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
251:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
244:
242:
	mov rax, QWORD PTR [rdi+200]
	add rax, rax
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+192]
	sub rax, 1
	mov QWORD PTR [rdi+192], rax
	jne 232b
	mov rax, QWORD PTR [rdi+184]
	add rax, 1
	mov QWORD PTR [rdi+184], rax
	cmp rax, QWORD PTR [rdi+160]
	jne 231b
	jmp 230f
229:
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
252:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 252b
	mov eax, 1
	mov QWORD PTR [rdi+216], rax
	mov eax, 16
	mov QWORD PTR [rdi+184], rax
253:
	mov rbx, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	mov eax, 0
	mov r14, 0
254:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
255:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
256:
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
	jne 256b
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
257:
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
	jne 257b
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
	jne 255b
	mov ebp, 0
	mov r14, 0
258:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 258b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
259:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rax, QWORD PTR [rdi+184]
	sub rax, 1
	mov QWORD PTR [rdi+184], rax
	jne 253b
230:
	mov rbx, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+72]
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
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
	mov rbx, QWORD PTR [rdi+112]
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+176]
	mov rax, rcx
	and rax, 7
	cmp rax, 0
	je 266f
	mov edx, 0
	mov r14, rsi
	add r14, rcx
268:
	mov rbp, rdx
	and rbp, 7
	je 269f
	jmp 270f
269:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
270:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 268b
	jmp 267f
266:
	mov r14, rsi
	add r14, rcx
	mov edx, 0
271:
	mov rax, QWORD PTR [rbx+rdx*1]
	and rax, r15
	bswap rax
	sub r14, 8
	mov QWORD PTR [r14], rax
	add rdx, 8
	cmp rdx, rcx
	jne 271b
267:
	mov rax, QWORD PTR [rdi+176]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 210f
29:
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov eax, 0
272:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 272b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
210:
	jmp 22f
21:
	mov eax, 0
	mov r10, rdi
	mov r11, rsi
273:
	mov BYTE PTR [r10], al
	add r10, 1
	sub r11, 1
	jne 273b
22:
	ret
	.p2align 6
