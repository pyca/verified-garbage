// The functions of `src/internal/vg_rsa_private_crt_precomputed_ifma512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_crt_precomputed_ifma512:
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
	mov rsi, QWORD PTR [rsp+104]
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rsi, rax
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
210:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 210b
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
	jb 211f
	jmp 212f
211:
	mov r12d, 2
212:
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
	jb 213f
	jmp 214f
213:
	mov r12d, 2
214:
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
215:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 215b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+152]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
216:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 217f
	jmp 218f
217:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
218:
	test rdx, rdx
	jne 216b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
219:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 219b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+224]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
220:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 221f
	jmp 222f
221:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
222:
	test rdx, rdx
	jne 220b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
223:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 223b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+184]
	mov rcx, QWORD PTR [rax+192]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
224:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 225f
	jmp 226f
225:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
226:
	test rdx, rdx
	jne 224b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
227:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 227b
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
228:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 228b
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
229:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 229b
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
230:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 230b
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
231:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 231b
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
	je 232f
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
	je 234f
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
	jmp 235f
234:
235:
	jmp 233f
232:
233:
	je 236f
	mov rax, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [rax+48]
	mov r12, QWORD PTR [rdi+48]
	mov ecx, 0
238:
	add rcx, rax
	cmp rcx, r12
	jb 238b
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
	jne 239f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 241f
243:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 243b
	jmp 242f
241:
242:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
244:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 245f
	jmp 246f
245:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
247:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 247b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
248:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 248b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
249:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 249b
246:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 244b
	jmp 240f
239:
	mov rcx, QWORD PTR [rdi+248]
	shr rcx, 6
	mov rdx, r12
	sub rdx, 1
	cmp rcx, rdx
	jb 250f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 252f
254:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 254b
	jmp 253f
252:
253:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
255:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 256f
	jmp 257f
256:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
258:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 258b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
259:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 259b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
260:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
257:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 255b
	jmp 251f
250:
	mov edx, 1
	mov r8, QWORD PTR [rdi+112]
	mov eax, 0
	mov r14, 0
261:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
251:
240:
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
262:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 262b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
263:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
264:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 265f
	mov r12, QWORD PTR [rdi+48]
	jmp 266f
265:
266:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
267:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
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
268:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 268b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
269:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 269b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
270:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 270b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 263b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
271:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
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
272:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
273:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
274:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 274b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 275f
	mov r12, QWORD PTR [rdi+48]
	jmp 276f
275:
276:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
277:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
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
278:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 278b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
279:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 279b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
280:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 280b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 273b
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
281:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 281b
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
282:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 282b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
283:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
284:
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
285:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 285b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 284b
286:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
287:
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
288:
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
289:
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
	jne 289b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 288b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 287b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 286b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+232]
	mov rax, QWORD PTR [rax+48]
	mov r12, QWORD PTR [rdi+48]
	mov ecx, 0
290:
	add rcx, rax
	cmp rcx, r12
	jb 290b
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
	jne 291f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 293f
295:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 295b
	jmp 294f
293:
294:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
296:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 297f
	jmp 298f
297:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
299:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 299b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
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
298:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 296b
	jmp 292f
291:
	mov rcx, QWORD PTR [rdi+248]
	shr rcx, 6
	mov rdx, r12
	sub rdx, 1
	cmp rcx, rdx
	jb 2102f
	mov rax, QWORD PTR [rdi+248]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 2104f
2106:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2106b
	jmp 2105f
2104:
2105:
	mov QWORD PTR [rdi+208], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
2107:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+248]
	and rax, QWORD PTR [rdi+208]
	jne 2108f
	jmp 2109f
2108:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2110:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2110b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2111:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2112:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2112b
2109:
	mov rax, QWORD PTR [rdi+208]
	shr rax, 1
	mov QWORD PTR [rdi+208], rax
	test rax, rax
	jne 2107b
	jmp 2103f
2102:
	mov edx, 1
	mov r8, QWORD PTR [rdi+112]
	mov eax, 0
	mov r14, 0
2113:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
2103:
292:
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2114:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2115:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2116:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2116b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2117f
	mov r12, QWORD PTR [rdi+48]
	jmp 2118f
2117:
2118:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2119:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
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
2120:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
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
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2115b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2123:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov rdi, QWORD PTR [rdi+128]
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2124:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2124b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+240]
	mov rsi, QWORD PTR [rax+112]
	mov r12, QWORD PTR [rax+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2125:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2125b
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
2126:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+112]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2127:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2128:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2128b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2129f
	mov r12, QWORD PTR [rdi+48]
	jmp 2130f
2129:
2130:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2131:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2131b
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
2132:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2132b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2133:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2134:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2127b
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
2135:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2135b
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
2136:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2136b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2137:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2137b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2138:
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
2139:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2139b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2138b
2140:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2141:
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
2142:
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
2143:
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
	jne 2143b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 2142b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2141b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2140b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2144:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+72]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2145:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2146:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2147f
	mov r12, QWORD PTR [rdi+48]
	jmp 2148f
2147:
2148:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2149:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2149b
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
2150:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2151:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2151b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2152:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2145b
	mov r8, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov rsi, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov ebp, 0
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
	mov r15, rbp
	mov ebp, 0
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2154:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2154b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2155:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2155b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+224]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2156:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2157f
	jmp 2158f
2157:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2158:
	test rdx, rdx
	jne 2156b
	mov r15, QWORD PTR [rdi+192]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2159:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov edx, 6
	mov ecx, 5
	mov r8d, 1
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
	jmp 237f
236:
	mov rdi, QWORD PTR [rdi+240]
	mov rsi, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rsi, rax
	add rax, rax
	add rax, rax
	add rsi, rax
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2160:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2160b
	mov rax, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rax+176]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2161:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov rax, r15
	xor rax, -1
	and rax, 1
	or rax, QWORD PTR [rbx]
	mov QWORD PTR [rbx], rax
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2162:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+104]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2163:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2164:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2165f
	mov r12, QWORD PTR [rdi+48]
	jmp 2166f
2165:
2166:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2167:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2167b
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
2168:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2169:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2170:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2170b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2163b
	mov edx, 5
	mov ecx, 6
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2171:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov rsi, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rsi, rax
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2172:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2172b
	mov rax, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rax+176]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2173:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov rax, r15
	xor rax, -1
	and rax, 1
	or rax, QWORD PTR [rbx]
	mov QWORD PTR [rbx], rax
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2174:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2174b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+104]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
2175:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2176:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2176b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 2177f
	mov r12, QWORD PTR [rdi+48]
	jmp 2178f
2177:
2178:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2179:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2179b
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
2180:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2180b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2181:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2181b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2182:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 2175b
	mov edx, 5
	mov ecx, 6
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2183:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
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
	je 2184f
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
	je 2186f
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
2188:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2188b
	mov ecx, 64
	mov QWORD PTR [rdi+240], rcx
2189:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2190:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2190b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2191:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2191b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2192:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2192b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2189b
	mov r8d, 5
2193:
	cmp r8, 5
	je 2194f
	cmp r8, 4
	je 2196f
	cmp r8, 3
	je 2198f
	cmp r8, 2
	je 2200f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 12608
	movabs r12, 4503599627370495
	jmp 2201f
2200:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 352
	movabs r12, 4503599627370495
2201:
	jmp 2199f
2198:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 672
	movabs r12, 4503599627370495
2199:
	jmp 2197f
2196:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 12256
	movabs r12, 4503599627370495
2197:
	jmp 2195f
2194:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	movabs r12, 4503599627370495
2195:
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
	jne 2193b
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
2202:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2202b
	mov r8, QWORD PTR [rdi+232]
	add r8, 11552
	mov r9, QWORD PTR [rdi+232]
	add r9, 11840
	mov ecx, 52
2203:
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
	jne 2203b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2204:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2204b
	mov ecx, 64
	mov QWORD PTR [rdi+240], rcx
2205:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2206:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2206b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2207:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2207b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2208:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2208b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2205b
	mov r8d, 5
2209:
	cmp r8, 5
	je 2210f
	cmp r8, 4
	je 2212f
	cmp r8, 3
	je 2214f
	cmp r8, 2
	je 2216f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 25536
	movabs r12, 4503599627370495
	jmp 2217f
2216:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 13280
	movabs r12, 4503599627370495
2217:
	jmp 2215f
2214:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 13600
	movabs r12, 4503599627370495
2215:
	jmp 2213f
2212:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 25184
	movabs r12, 4503599627370495
2213:
	jmp 2211f
2210:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 12928
	movabs r12, 4503599627370495
2211:
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
	jne 2209b
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
2218:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2218b
	mov r8, QWORD PTR [rdi+232]
	add r8, 24480
	mov r9, QWORD PTR [rdi+232]
	add r9, 24768
	mov ecx, 52
2219:
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
	jne 2219b
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
2220:
	cmp r13, 1952
	jb 2221f
	mov r8, rbx
	add r8, r13
	sub r8, 320
	mov r9, rbx
	add r9, 672
	mov r11, rbx
	add r11, r13
	jmp 2222f
2221:
	mov r8, rbx
	add r8, r13
	sub r8, 960
	mov r9, rbx
	add r9, 12256
	mov r11, r8
2222:
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
2223:
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
	jne 2223b
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
	je 2224f
	jmp 2225f
2224:
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
2225:
	add r13, 320
	cmp r13, 11552
	jne 2220b
	mov r13d, 6
2226:
	cmp r13, 416
	je 2227f
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
2229:
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
	jne 2229b
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
2230:
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
	jne 2230b
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
	jmp 2228f
2227:
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
2228:
2231:
	cmp r15, 1
	je 2232f
	mov r8, rbx
	add r8, 352
	mov r9, rbx
	add r9, 352
	mov r11, rbx
	add r11, 352
	jmp 2233f
2232:
	mov r8, rbx
	add r8, 352
	mov r9, rbx
	add r9, 992
	mov r11, rbx
	add r11, 352
2233:
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
2234:
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
	jne 2234b
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
	jne 2231b
	add r13, 1
	cmp r13, 417
	jne 2226b
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
2235:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2235b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2236:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2236b
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
2237:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2237b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2238:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2238b
	mov rdi, QWORD PTR [rdi+128]
	jmp 2187f
2186:
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
2239:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2239b
	mov ecx, 48
	mov QWORD PTR [rdi+240], rcx
2240:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2241:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2241b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2242:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2242b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2243:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2243b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2240b
	mov r8d, 5
2244:
	cmp r8, 5
	je 2245f
	cmp r8, 4
	je 2247f
	cmp r8, 3
	je 2249f
	cmp r8, 2
	je 2251f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10080
	movabs r12, 4503599627370495
	jmp 2252f
2251:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 288
	movabs r12, 4503599627370495
2252:
	jmp 2250f
2249:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 544
	movabs r12, 4503599627370495
2250:
	jmp 2248f
2247:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 9792
	movabs r12, 4503599627370495
2248:
	jmp 2246f
2245:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	movabs r12, 4503599627370495
2246:
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
	jne 2244b
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
2253:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2253b
	mov r8, QWORD PTR [rdi+232]
	add r8, 9248
	mov r9, QWORD PTR [rdi+232]
	add r9, 9472
	mov ecx, 39
2254:
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
	jne 2254b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2255:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2255b
	mov ecx, 48
	mov QWORD PTR [rdi+240], rcx
2256:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2257:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2257b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2258:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2258b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2259:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2259b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2256b
	mov r8d, 5
2260:
	cmp r8, 5
	je 2261f
	cmp r8, 4
	je 2263f
	cmp r8, 3
	je 2265f
	cmp r8, 2
	je 2267f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 20416
	movabs r12, 4503599627370495
	jmp 2268f
2267:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10624
	movabs r12, 4503599627370495
2268:
	jmp 2266f
2265:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10880
	movabs r12, 4503599627370495
2266:
	jmp 2264f
2263:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 20128
	movabs r12, 4503599627370495
2264:
	jmp 2262f
2261:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10336
	movabs r12, 4503599627370495
2262:
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
	jne 2260b
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
2269:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2269b
	mov r8, QWORD PTR [rdi+232]
	add r8, 19584
	mov r9, QWORD PTR [rdi+232]
	add r9, 19808
	mov ecx, 39
2270:
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
	jne 2270b
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
2271:
	cmp r13, 1568
	jb 2272f
	mov r8, rbx
	add r8, r13
	sub r8, 256
	mov r9, rbx
	add r9, 544
	mov r11, rbx
	add r11, r13
	jmp 2273f
2272:
	mov r8, rbx
	add r8, r13
	sub r8, 768
	mov r9, rbx
	add r9, 9792
	mov r11, r8
2273:
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
2274:
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
	jne 2274b
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
	je 2275f
	jmp 2276f
2275:
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
2276:
	add r13, 256
	cmp r13, 9248
	jne 2271b
	mov r13d, 4
2277:
	cmp r13, 312
	je 2278f
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
2280:
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
	jne 2280b
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
2281:
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
	jne 2281b
	vmovdqu64 YMMWORD PTR [rbx+11136], ymm0
	vmovdqu64 YMMWORD PTR [rbx+11168], ymm1
	vmovdqu64 YMMWORD PTR [rbx+11200], ymm2
	vmovdqu64 YMMWORD PTR [rbx+11232], ymm3
	vmovdqu64 YMMWORD PTR [rbx+11264], ymm4
	vmovdqu64 YMMWORD PTR [rbx+11296], ymm5
	vmovdqu64 YMMWORD PTR [rbx+11328], ymm6
	vmovdqu64 YMMWORD PTR [rbx+11360], ymm7
	mov r15d, 6
	jmp 2279f
2278:
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
2279:
2282:
	cmp r15, 1
	je 2283f
	mov r8, rbx
	add r8, 288
	mov r9, rbx
	add r9, 288
	mov r11, rbx
	add r11, 288
	jmp 2284f
2283:
	mov r8, rbx
	add r8, 288
	mov r9, rbx
	add r9, 800
	mov r11, rbx
	add r11, 288
2284:
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
2285:
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
	jne 2285b
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
	jne 2282b
	add r13, 1
	cmp r13, 313
	jne 2277b
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
2286:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2286b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2287:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2287b
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
2288:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2288b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2289:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2289b
	mov rdi, QWORD PTR [rdi+128]
2187:
	jmp 2185f
2184:
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
2290:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2290b
	mov ecx, 34
	mov QWORD PTR [rdi+240], rcx
2291:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2292:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2292b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2293:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2293b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2294:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2294b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2291b
	mov r8d, 5
2295:
	cmp r8, 5
	je 2296f
	cmp r8, 4
	je 2298f
	cmp r8, 3
	je 2300f
	cmp r8, 2
	je 2302f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 4224
	movabs r12, 4503599627370495
	jmp 2303f
2302:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 224
	movabs r12, 4503599627370495
2303:
	jmp 2301f
2300:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 416
	movabs r12, 4503599627370495
2301:
	jmp 2299f
2298:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 4000
	movabs r12, 4503599627370495
2299:
	jmp 2297f
2296:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	movabs r12, 4503599627370495
2297:
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
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov eax, 0
	mov QWORD PTR [r11+88], rax
	mov eax, 0
	mov QWORD PTR [r11+120], rax
	mov eax, 0
	mov QWORD PTR [r11+152], rax
	mov eax, 0
	mov QWORD PTR [r11+184], rax
	sub r8, 1
	jne 2295b
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+192], rax
	mov QWORD PTR [r11+200], rax
	mov QWORD PTR [r11+208], rax
	mov QWORD PTR [r11+216], rax
	mov eax, 0
	mov QWORD PTR [r11+3872], rax
	mov QWORD PTR [r11+3880], rax
	mov QWORD PTR [r11+3888], rax
	mov QWORD PTR [r11+3896], rax
	mov QWORD PTR [r11+3904], rax
	mov QWORD PTR [r11+3912], rax
	mov QWORD PTR [r11+3920], rax
	mov QWORD PTR [r11+3928], rax
	mov QWORD PTR [r11+3936], rax
	mov QWORD PTR [r11+3944], rax
	mov QWORD PTR [r11+3952], rax
	mov QWORD PTR [r11+3960], rax
	mov QWORD PTR [r11+3968], rax
	mov QWORD PTR [r11+3976], rax
	mov QWORD PTR [r11+3984], rax
	mov QWORD PTR [r11+3992], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+200]
	mov rcx, QWORD PTR [rax+160]
	add r11, 4000
	sub r11, rcx
2304:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2304b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2305:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2305b
	mov ecx, 34
	mov QWORD PTR [rdi+240], rcx
2306:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2307:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2307b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
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
	sbb rbp, rbp
	mov r14, 0
2309:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2309b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 2306b
	mov r8d, 5
2310:
	cmp r8, 5
	je 2311f
	cmp r8, 4
	je 2313f
	cmp r8, 3
	je 2315f
	cmp r8, 2
	je 2317f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 9024
	movabs r12, 4503599627370495
	jmp 2318f
2317:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 5024
	movabs r12, 4503599627370495
2318:
	jmp 2316f
2315:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 5216
	movabs r12, 4503599627370495
2316:
	jmp 2314f
2313:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 8800
	movabs r12, 4503599627370495
2314:
	jmp 2312f
2311:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 4800
	movabs r12, 4503599627370495
2312:
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
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov eax, 0
	mov QWORD PTR [r11+88], rax
	mov eax, 0
	mov QWORD PTR [r11+120], rax
	mov eax, 0
	mov QWORD PTR [r11+152], rax
	mov eax, 0
	mov QWORD PTR [r11+184], rax
	sub r8, 1
	jne 2310b
	mov r11, QWORD PTR [rdi+232]
	add r11, 4800
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+192], rax
	mov QWORD PTR [r11+200], rax
	mov QWORD PTR [r11+208], rax
	mov QWORD PTR [r11+216], rax
	mov eax, 0
	mov QWORD PTR [r11+3872], rax
	mov QWORD PTR [r11+3880], rax
	mov QWORD PTR [r11+3888], rax
	mov QWORD PTR [r11+3896], rax
	mov QWORD PTR [r11+3904], rax
	mov QWORD PTR [r11+3912], rax
	mov QWORD PTR [r11+3920], rax
	mov QWORD PTR [r11+3928], rax
	mov QWORD PTR [r11+3936], rax
	mov QWORD PTR [r11+3944], rax
	mov QWORD PTR [r11+3952], rax
	mov QWORD PTR [r11+3960], rax
	mov QWORD PTR [r11+3968], rax
	mov QWORD PTR [r11+3976], rax
	mov QWORD PTR [r11+3984], rax
	mov QWORD PTR [r11+3992], rax
	mov QWORD PTR [r11+4224], rax
	mov QWORD PTR [r11+4256], rax
	mov QWORD PTR [r11+4288], rax
	mov QWORD PTR [r11+4320], rax
	mov QWORD PTR [r11+4352], rax
	mov QWORD PTR [r11+4384], rax
	mov QWORD PTR [r11+4232], rax
	mov QWORD PTR [r11+4264], rax
	mov QWORD PTR [r11+4296], rax
	mov QWORD PTR [r11+4328], rax
	mov QWORD PTR [r11+4360], rax
	mov QWORD PTR [r11+4392], rax
	mov QWORD PTR [r11+4240], rax
	mov QWORD PTR [r11+4272], rax
	mov QWORD PTR [r11+4304], rax
	mov QWORD PTR [r11+4336], rax
	mov QWORD PTR [r11+4368], rax
	mov QWORD PTR [r11+4400], rax
	mov QWORD PTR [r11+4248], rax
	mov QWORD PTR [r11+4280], rax
	mov QWORD PTR [r11+4312], rax
	mov QWORD PTR [r11+4344], rax
	mov QWORD PTR [r11+4376], rax
	mov QWORD PTR [r11+4408], rax
	mov eax, 1
	mov QWORD PTR [r11+4224], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+216]
	mov rcx, QWORD PTR [rax+192]
	add r11, 4000
	sub r11, rcx
2319:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 2319b
	mov rbx, QWORD PTR [rdi+232]
	stmxcsr DWORD PTR [rbx+9600]
	mov r11d, DWORD PTR [rbx+9600]
	and r11d, 65535
	mov DWORD PTR [rbx+9600], r11d
	mov eax, 8127
	mov DWORD PTR [rbx+9604], eax
	ldmxcsr DWORD PTR [rbx+9604]
	lfence
	mov eax, 0
	mov QWORD PTR [rbx+608], rax
	mov QWORD PTR [rbx+640], rax
	mov QWORD PTR [rbx+672], rax
	mov QWORD PTR [rbx+704], rax
	mov QWORD PTR [rbx+736], rax
	mov QWORD PTR [rbx+768], rax
	mov QWORD PTR [rbx+616], rax
	mov QWORD PTR [rbx+648], rax
	mov QWORD PTR [rbx+680], rax
	mov QWORD PTR [rbx+712], rax
	mov QWORD PTR [rbx+744], rax
	mov QWORD PTR [rbx+776], rax
	mov QWORD PTR [rbx+624], rax
	mov QWORD PTR [rbx+656], rax
	mov QWORD PTR [rbx+688], rax
	mov QWORD PTR [rbx+720], rax
	mov QWORD PTR [rbx+752], rax
	mov QWORD PTR [rbx+784], rax
	mov QWORD PTR [rbx+632], rax
	mov QWORD PTR [rbx+664], rax
	mov QWORD PTR [rbx+696], rax
	mov QWORD PTR [rbx+728], rax
	mov QWORD PTR [rbx+760], rax
	mov QWORD PTR [rbx+792], rax
	movabs rax, 1
	mov QWORD PTR [rbx+744], rax
	mov eax, 0
	mov QWORD PTR [rbx+5408], rax
	mov QWORD PTR [rbx+5440], rax
	mov QWORD PTR [rbx+5472], rax
	mov QWORD PTR [rbx+5504], rax
	mov QWORD PTR [rbx+5536], rax
	mov QWORD PTR [rbx+5568], rax
	mov QWORD PTR [rbx+5416], rax
	mov QWORD PTR [rbx+5448], rax
	mov QWORD PTR [rbx+5480], rax
	mov QWORD PTR [rbx+5512], rax
	mov QWORD PTR [rbx+5544], rax
	mov QWORD PTR [rbx+5576], rax
	mov QWORD PTR [rbx+5424], rax
	mov QWORD PTR [rbx+5456], rax
	mov QWORD PTR [rbx+5488], rax
	mov QWORD PTR [rbx+5520], rax
	mov QWORD PTR [rbx+5552], rax
	mov QWORD PTR [rbx+5584], rax
	mov QWORD PTR [rbx+5432], rax
	mov QWORD PTR [rbx+5464], rax
	mov QWORD PTR [rbx+5496], rax
	mov QWORD PTR [rbx+5528], rax
	mov QWORD PTR [rbx+5560], rax
	mov QWORD PTR [rbx+5592], rax
	movabs rax, 1
	mov QWORD PTR [rbx+5544], rax
	mov r8, rbx
	add r8, 608
	mov r9, rbx
	add r9, 608
	mov r11, rbx
	add r11, 4416
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
2320:
	mov rax, QWORD PTR [r9]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4800]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm0, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm6, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm0, 52
	vmovq xmm17, xmm17
	vpaddq ymm1, ymm1, ymm17
	valignq ymm0, ymm16, ymm0, 1
	vpsrlq ymm17, ymm6, 52
	vmovq xmm17, xmm17
	vpaddq ymm7, ymm7, ymm17
	valignq ymm6, ymm16, ymm6, 1
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4832]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm1, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm7, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm1, 52
	vmovq xmm17, xmm17
	vpaddq ymm2, ymm2, ymm17
	valignq ymm1, ymm16, ymm1, 1
	vpsrlq ymm17, ymm7, 52
	vmovq xmm17, xmm17
	vpaddq ymm8, ymm8, ymm17
	valignq ymm7, ymm16, ymm7, 1
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4864]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm2, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm8, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm2, 52
	vmovq xmm17, xmm17
	vpaddq ymm3, ymm3, ymm17
	valignq ymm2, ymm16, ymm2, 1
	vpsrlq ymm17, ymm8, 52
	vmovq xmm17, xmm17
	vpaddq ymm9, ymm9, ymm17
	valignq ymm8, ymm16, ymm8, 1
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4896]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm3, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm9, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm3, 52
	vmovq xmm17, xmm17
	vpaddq ymm4, ymm4, ymm17
	valignq ymm3, ymm16, ymm3, 1
	vpsrlq ymm17, ymm9, 52
	vmovq xmm17, xmm17
	vpaddq ymm10, ymm10, ymm17
	valignq ymm9, ymm16, ymm9, 1
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4928]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm4, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm4, 52
	vmovq xmm17, xmm17
	vpaddq ymm5, ymm5, ymm17
	valignq ymm4, ymm16, ymm4, 1
	vpsrlq ymm17, ymm10, 52
	vmovq xmm17, xmm17
	vpaddq ymm11, ymm11, ymm17
	valignq ymm10, ymm16, ymm10, 1
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4960]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm5, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm5, 52
	vmovq xmm17, xmm17
	vpaddq ymm0, ymm0, ymm17
	valignq ymm5, ymm16, ymm5, 1
	vpsrlq ymm17, ymm11, 52
	vmovq xmm17, xmm17
	vpaddq ymm6, ymm6, ymm17
	valignq ymm11, ymm16, ymm11, 1
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4960]
	add r9, 8
	sub rcx, 1
	jne 2320b
	mov rax, QWORD PTR [r9]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4800]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm0, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm6, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm0, 52
	vmovq xmm17, xmm17
	vpaddq ymm1, ymm1, ymm17
	valignq ymm0, ymm16, ymm0, 1
	vpsrlq ymm17, ymm6, 52
	vmovq xmm17, xmm17
	vpaddq ymm7, ymm7, ymm17
	valignq ymm6, ymm16, ymm6, 1
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4832]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm1, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm7, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm1, 52
	vmovq xmm17, xmm17
	vpaddq ymm2, ymm2, ymm17
	valignq ymm1, ymm16, ymm1, 1
	vpsrlq ymm17, ymm7, 52
	vmovq xmm17, xmm17
	vpaddq ymm8, ymm8, ymm17
	valignq ymm7, ymm16, ymm7, 1
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4864]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm2, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm8, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm2, 52
	vmovq xmm17, xmm17
	vpaddq ymm3, ymm3, ymm17
	valignq ymm2, ymm16, ymm2, 1
	vpsrlq ymm17, ymm8, 52
	vmovq xmm17, xmm17
	vpaddq ymm9, ymm9, ymm17
	valignq ymm8, ymm16, ymm8, 1
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4896]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm3, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm9, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm3, 52
	vmovq xmm17, xmm17
	vpaddq ymm4, ymm4, ymm17
	valignq ymm3, ymm16, ymm3, 1
	vpsrlq ymm17, ymm9, 52
	vmovq xmm17, xmm17
	vpaddq ymm10, ymm10, ymm17
	valignq ymm9, ymm16, ymm9, 1
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4960]
	vmovdqu64 YMMWORD PTR [r11], ymm4
	vmovdqu64 YMMWORD PTR [r11+32], ymm5
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vmovdqu64 YMMWORD PTR [r11+4800], ymm10
	vmovdqu64 YMMWORD PTR [r11+4832], ymm11
	vmovdqu64 YMMWORD PTR [r11+4864], ymm6
	vmovdqu64 YMMWORD PTR [r11+4896], ymm7
	vmovdqu64 YMMWORD PTR [r11+4928], ymm8
	vmovdqu64 YMMWORD PTR [r11+4960], ymm9
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4864], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4896]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4896], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4872]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4872], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4904]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4904], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4880]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4880], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4912]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4912], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4888]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4888], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4920]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4920], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4984], rcx
	shr rsi, 52
	mov eax, 0
	mov QWORD PTR [rbx+608], rax
	mov QWORD PTR [rbx+640], rax
	mov QWORD PTR [rbx+672], rax
	mov QWORD PTR [rbx+704], rax
	mov QWORD PTR [rbx+736], rax
	mov QWORD PTR [rbx+768], rax
	mov QWORD PTR [rbx+616], rax
	mov QWORD PTR [rbx+648], rax
	mov QWORD PTR [rbx+680], rax
	mov QWORD PTR [rbx+712], rax
	mov QWORD PTR [rbx+744], rax
	mov QWORD PTR [rbx+776], rax
	mov QWORD PTR [rbx+624], rax
	mov QWORD PTR [rbx+656], rax
	mov QWORD PTR [rbx+688], rax
	mov QWORD PTR [rbx+720], rax
	mov QWORD PTR [rbx+752], rax
	mov QWORD PTR [rbx+784], rax
	mov QWORD PTR [rbx+632], rax
	mov QWORD PTR [rbx+664], rax
	mov QWORD PTR [rbx+696], rax
	mov QWORD PTR [rbx+728], rax
	mov QWORD PTR [rbx+760], rax
	mov QWORD PTR [rbx+792], rax
	movabs rax, 2251799813685248
	mov QWORD PTR [rbx+792], rax
	mov eax, 0
	mov QWORD PTR [rbx+5408], rax
	mov QWORD PTR [rbx+5440], rax
	mov QWORD PTR [rbx+5472], rax
	mov QWORD PTR [rbx+5504], rax
	mov QWORD PTR [rbx+5536], rax
	mov QWORD PTR [rbx+5568], rax
	mov QWORD PTR [rbx+5416], rax
	mov QWORD PTR [rbx+5448], rax
	mov QWORD PTR [rbx+5480], rax
	mov QWORD PTR [rbx+5512], rax
	mov QWORD PTR [rbx+5544], rax
	mov QWORD PTR [rbx+5576], rax
	mov QWORD PTR [rbx+5424], rax
	mov QWORD PTR [rbx+5456], rax
	mov QWORD PTR [rbx+5488], rax
	mov QWORD PTR [rbx+5520], rax
	mov QWORD PTR [rbx+5552], rax
	mov QWORD PTR [rbx+5584], rax
	mov QWORD PTR [rbx+5432], rax
	mov QWORD PTR [rbx+5464], rax
	mov QWORD PTR [rbx+5496], rax
	mov QWORD PTR [rbx+5528], rax
	mov QWORD PTR [rbx+5560], rax
	mov QWORD PTR [rbx+5592], rax
	movabs rax, 2251799813685248
	mov QWORD PTR [rbx+5592], rax
	mov r8, rbx
	add r8, 608
	mov r9, rbx
	add r9, 4000
	mov r11, rbx
	add r11, 4000
	mov r10, rbx
	mov ecx, 3
	movabs rax, 4503599627370495
	vmovq xmm30, rax
	vpermq zmm30, zmm30, 64
	vinserti64x4 zmm30, zmm30, ymm30, 1
	vmovdqu64 ymm17, YMMWORD PTR [r8]
	vinserti64x4 zmm17, zmm17, YMMWORD PTR [r8+4800], 1
	vmovdqu64 ymm18, YMMWORD PTR [r8+32]
	vinserti64x4 zmm18, zmm18, YMMWORD PTR [r8+4832], 1
	vmovdqu64 ymm19, YMMWORD PTR [r8+64]
	vinserti64x4 zmm19, zmm19, YMMWORD PTR [r8+4864], 1
	vmovdqu64 ymm20, YMMWORD PTR [r8+96]
	vinserti64x4 zmm20, zmm20, YMMWORD PTR [r8+4896], 1
	vmovdqu64 ymm21, YMMWORD PTR [r8+128]
	vinserti64x4 zmm21, zmm21, YMMWORD PTR [r8+4928], 1
	vmovdqu64 ymm22, YMMWORD PTR [r8+160]
	vinserti64x4 zmm22, zmm22, YMMWORD PTR [r8+4960], 1
	vmovdqu64 ymm24, YMMWORD PTR [r10+4416]
	vinserti64x4 zmm24, zmm24, YMMWORD PTR [r10+9216], 1
	vmovdqu64 ymm25, YMMWORD PTR [r10+4448]
	vinserti64x4 zmm25, zmm25, YMMWORD PTR [r10+9248], 1
	vmovdqu64 ymm26, YMMWORD PTR [r10+4480]
	vinserti64x4 zmm26, zmm26, YMMWORD PTR [r10+9280], 1
	vmovdqu64 ymm27, YMMWORD PTR [r10+4512]
	vinserti64x4 zmm27, zmm27, YMMWORD PTR [r10+9312], 1
	vmovdqu64 ymm28, YMMWORD PTR [r10+4544]
	vinserti64x4 zmm28, zmm28, YMMWORD PTR [r10+9344], 1
	vmovdqu64 ymm29, YMMWORD PTR [r10+4576]
	vinserti64x4 zmm29, zmm29, YMMWORD PTR [r10+9376], 1
	vpermq zmm23, zmm29, 147
	vpxorq zmm0, zmm0, zmm0
	vpxorq zmm1, zmm1, zmm1
	vpxorq zmm2, zmm2, zmm2
	vpxorq zmm3, zmm3, zmm3
	vpxorq zmm4, zmm4, zmm4
	vpxorq zmm5, zmm5, zmm5
	vpxorq zmm6, zmm6, zmm6
	vpxorq zmm7, zmm7, zmm7
	vpxorq zmm8, zmm8, zmm8
	vpxorq zmm9, zmm9, zmm9
	vpxorq zmm10, zmm10, zmm10
	vpxorq zmm11, zmm11, zmm11
	vpxorq zmm15, zmm15, zmm15
	vpbroadcastq ymm12, QWORD PTR [r9]
	vpbroadcastq ymm31, QWORD PTR [r9+4800]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
2321:
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpbroadcastq ymm12, QWORD PTR [r9+128]
	vpbroadcastq ymm31, QWORD PTR [r9+4928]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm4, zmm12, zmm17
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpaddq zmm10, zmm10, zmm4
	vpermq zmm14, zmm10, 0
	vpsrlq zmm16, zmm10, 52
	vpbroadcastq ymm13, QWORD PTR [r9+160]
	vpbroadcastq ymm31, QWORD PTR [r9+4960]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm5, zmm13, zmm17
	vpmadd52luq zmm5, zmm12, zmm18
	vpmadd52huq zmm5, zmm12, zmm17
	vpaddq zmm5, zmm5, zmm16
	vpermq zmm10, zmm10, 249
	vpandq zmm10, zmm10, zmm30
	vpxorq zmm4, zmm4, zmm4
	vpmadd52huq zmm10, zmm15, zmm28
	vpmadd52luq zmm10, zmm15, zmm29
	vpmadd52luq zmm10, zmm14, zmm28
	vpmadd52luq zmm0, zmm12, zmm19
	vpmadd52huq zmm0, zmm12, zmm18
	vpmadd52luq zmm6, zmm14, zmm24
	vpmadd52huq zmm6, zmm14, zmm23
	vpmadd52luq zmm1, zmm12, zmm20
	vpmadd52huq zmm1, zmm12, zmm19
	vpmadd52luq zmm7, zmm14, zmm25
	vpmadd52huq zmm7, zmm14, zmm24
	vpmadd52luq zmm2, zmm12, zmm21
	vpmadd52huq zmm2, zmm12, zmm20
	vpmadd52luq zmm8, zmm14, zmm26
	vpmadd52huq zmm8, zmm14, zmm25
	vpmadd52luq zmm3, zmm12, zmm22
	vpmadd52huq zmm3, zmm12, zmm21
	vpmadd52luq zmm9, zmm14, zmm27
	vpmadd52huq zmm9, zmm14, zmm26
	vpmadd52huq zmm4, zmm12, zmm22
	vpmadd52huq zmm10, zmm14, zmm27
	vpaddq zmm11, zmm11, zmm5
	vpermq zmm15, zmm11, 0
	vpsrlq zmm16, zmm11, 52
	vpbroadcastq ymm12, QWORD PTR [r9+8]
	vpbroadcastq ymm31, QWORD PTR [r9+4808]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
	vpmadd52luq zmm0, zmm13, zmm18
	vpmadd52huq zmm0, zmm13, zmm17
	vpaddq zmm0, zmm0, zmm16
	vpermq zmm11, zmm11, 249
	vpandq zmm11, zmm11, zmm30
	vpxorq zmm5, zmm5, zmm5
	vpmadd52huq zmm11, zmm14, zmm28
	vpmadd52luq zmm11, zmm14, zmm29
	vpmadd52luq zmm11, zmm15, zmm28
	vpmadd52luq zmm1, zmm13, zmm19
	vpmadd52huq zmm1, zmm13, zmm18
	vpmadd52luq zmm7, zmm15, zmm24
	vpmadd52huq zmm7, zmm15, zmm23
	vpmadd52luq zmm2, zmm13, zmm20
	vpmadd52huq zmm2, zmm13, zmm19
	vpmadd52luq zmm8, zmm15, zmm25
	vpmadd52huq zmm8, zmm15, zmm24
	vpmadd52luq zmm3, zmm13, zmm21
	vpmadd52huq zmm3, zmm13, zmm20
	vpmadd52luq zmm9, zmm15, zmm26
	vpmadd52huq zmm9, zmm15, zmm25
	vpmadd52luq zmm4, zmm13, zmm22
	vpmadd52huq zmm4, zmm13, zmm21
	vpmadd52luq zmm10, zmm15, zmm27
	vpmadd52huq zmm10, zmm15, zmm26
	vpmadd52huq zmm5, zmm13, zmm22
	vpmadd52huq zmm11, zmm15, zmm27
	add r9, 8
	sub rcx, 1
	jne 2321b
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpermq zmm31, zmm28, 147
	vpmadd52huq zmm10, zmm15, zmm31
	vpmadd52luq zmm10, zmm15, zmm23
	vpaddq zmm4, zmm4, zmm10
	vpaddq zmm5, zmm5, zmm11
	vpaddq zmm0, zmm0, zmm6
	vpaddq zmm1, zmm1, zmm7
	vpaddq zmm2, zmm2, zmm8
	vpaddq zmm3, zmm3, zmm9
	vmovdqu64 YMMWORD PTR [r11], ymm4
	vextracti64x4 YMMWORD PTR [r11+4800], zmm4, 1
	vmovdqu64 YMMWORD PTR [r11+32], ymm5
	vextracti64x4 YMMWORD PTR [r11+4832], zmm5, 1
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vextracti64x4 YMMWORD PTR [r11+4864], zmm0, 1
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vextracti64x4 YMMWORD PTR [r11+4896], zmm1, 1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vextracti64x4 YMMWORD PTR [r11+4928], zmm2, 1
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vextracti64x4 YMMWORD PTR [r11+4960], zmm3, 1
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4864], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4896]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4896], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4872]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4872], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4904]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4904], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4880]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4880], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4912]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4912], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4888]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4888], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4920]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4920], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4984], rcx
	shr rsi, 52
	mov r8, rbx
	add r8, 608
	mov r9, rbx
	add r9, 224
	mov r11, rbx
	add r11, 224
	mov r10, rbx
	mov ecx, 3
	movabs rax, 4503599627370495
	vmovq xmm30, rax
	vpermq zmm30, zmm30, 64
	vinserti64x4 zmm30, zmm30, ymm30, 1
	vmovdqu64 ymm17, YMMWORD PTR [r8]
	vinserti64x4 zmm17, zmm17, YMMWORD PTR [r8+4800], 1
	vmovdqu64 ymm18, YMMWORD PTR [r8+32]
	vinserti64x4 zmm18, zmm18, YMMWORD PTR [r8+4832], 1
	vmovdqu64 ymm19, YMMWORD PTR [r8+64]
	vinserti64x4 zmm19, zmm19, YMMWORD PTR [r8+4864], 1
	vmovdqu64 ymm20, YMMWORD PTR [r8+96]
	vinserti64x4 zmm20, zmm20, YMMWORD PTR [r8+4896], 1
	vmovdqu64 ymm21, YMMWORD PTR [r8+128]
	vinserti64x4 zmm21, zmm21, YMMWORD PTR [r8+4928], 1
	vmovdqu64 ymm22, YMMWORD PTR [r8+160]
	vinserti64x4 zmm22, zmm22, YMMWORD PTR [r8+4960], 1
	vmovdqu64 ymm24, YMMWORD PTR [r10+4416]
	vinserti64x4 zmm24, zmm24, YMMWORD PTR [r10+9216], 1
	vmovdqu64 ymm25, YMMWORD PTR [r10+4448]
	vinserti64x4 zmm25, zmm25, YMMWORD PTR [r10+9248], 1
	vmovdqu64 ymm26, YMMWORD PTR [r10+4480]
	vinserti64x4 zmm26, zmm26, YMMWORD PTR [r10+9280], 1
	vmovdqu64 ymm27, YMMWORD PTR [r10+4512]
	vinserti64x4 zmm27, zmm27, YMMWORD PTR [r10+9312], 1
	vmovdqu64 ymm28, YMMWORD PTR [r10+4544]
	vinserti64x4 zmm28, zmm28, YMMWORD PTR [r10+9344], 1
	vmovdqu64 ymm29, YMMWORD PTR [r10+4576]
	vinserti64x4 zmm29, zmm29, YMMWORD PTR [r10+9376], 1
	vpermq zmm23, zmm29, 147
	vpxorq zmm0, zmm0, zmm0
	vpxorq zmm1, zmm1, zmm1
	vpxorq zmm2, zmm2, zmm2
	vpxorq zmm3, zmm3, zmm3
	vpxorq zmm4, zmm4, zmm4
	vpxorq zmm5, zmm5, zmm5
	vpxorq zmm6, zmm6, zmm6
	vpxorq zmm7, zmm7, zmm7
	vpxorq zmm8, zmm8, zmm8
	vpxorq zmm9, zmm9, zmm9
	vpxorq zmm10, zmm10, zmm10
	vpxorq zmm11, zmm11, zmm11
	vpxorq zmm15, zmm15, zmm15
	vpbroadcastq ymm12, QWORD PTR [r9]
	vpbroadcastq ymm31, QWORD PTR [r9+4800]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
2322:
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpbroadcastq ymm12, QWORD PTR [r9+128]
	vpbroadcastq ymm31, QWORD PTR [r9+4928]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm4, zmm12, zmm17
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpaddq zmm10, zmm10, zmm4
	vpermq zmm14, zmm10, 0
	vpsrlq zmm16, zmm10, 52
	vpbroadcastq ymm13, QWORD PTR [r9+160]
	vpbroadcastq ymm31, QWORD PTR [r9+4960]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm5, zmm13, zmm17
	vpmadd52luq zmm5, zmm12, zmm18
	vpmadd52huq zmm5, zmm12, zmm17
	vpaddq zmm5, zmm5, zmm16
	vpermq zmm10, zmm10, 249
	vpandq zmm10, zmm10, zmm30
	vpxorq zmm4, zmm4, zmm4
	vpmadd52huq zmm10, zmm15, zmm28
	vpmadd52luq zmm10, zmm15, zmm29
	vpmadd52luq zmm10, zmm14, zmm28
	vpmadd52luq zmm0, zmm12, zmm19
	vpmadd52huq zmm0, zmm12, zmm18
	vpmadd52luq zmm6, zmm14, zmm24
	vpmadd52huq zmm6, zmm14, zmm23
	vpmadd52luq zmm1, zmm12, zmm20
	vpmadd52huq zmm1, zmm12, zmm19
	vpmadd52luq zmm7, zmm14, zmm25
	vpmadd52huq zmm7, zmm14, zmm24
	vpmadd52luq zmm2, zmm12, zmm21
	vpmadd52huq zmm2, zmm12, zmm20
	vpmadd52luq zmm8, zmm14, zmm26
	vpmadd52huq zmm8, zmm14, zmm25
	vpmadd52luq zmm3, zmm12, zmm22
	vpmadd52huq zmm3, zmm12, zmm21
	vpmadd52luq zmm9, zmm14, zmm27
	vpmadd52huq zmm9, zmm14, zmm26
	vpmadd52huq zmm4, zmm12, zmm22
	vpmadd52huq zmm10, zmm14, zmm27
	vpaddq zmm11, zmm11, zmm5
	vpermq zmm15, zmm11, 0
	vpsrlq zmm16, zmm11, 52
	vpbroadcastq ymm12, QWORD PTR [r9+8]
	vpbroadcastq ymm31, QWORD PTR [r9+4808]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
	vpmadd52luq zmm0, zmm13, zmm18
	vpmadd52huq zmm0, zmm13, zmm17
	vpaddq zmm0, zmm0, zmm16
	vpermq zmm11, zmm11, 249
	vpandq zmm11, zmm11, zmm30
	vpxorq zmm5, zmm5, zmm5
	vpmadd52huq zmm11, zmm14, zmm28
	vpmadd52luq zmm11, zmm14, zmm29
	vpmadd52luq zmm11, zmm15, zmm28
	vpmadd52luq zmm1, zmm13, zmm19
	vpmadd52huq zmm1, zmm13, zmm18
	vpmadd52luq zmm7, zmm15, zmm24
	vpmadd52huq zmm7, zmm15, zmm23
	vpmadd52luq zmm2, zmm13, zmm20
	vpmadd52huq zmm2, zmm13, zmm19
	vpmadd52luq zmm8, zmm15, zmm25
	vpmadd52huq zmm8, zmm15, zmm24
	vpmadd52luq zmm3, zmm13, zmm21
	vpmadd52huq zmm3, zmm13, zmm20
	vpmadd52luq zmm9, zmm15, zmm26
	vpmadd52huq zmm9, zmm15, zmm25
	vpmadd52luq zmm4, zmm13, zmm22
	vpmadd52huq zmm4, zmm13, zmm21
	vpmadd52luq zmm10, zmm15, zmm27
	vpmadd52huq zmm10, zmm15, zmm26
	vpmadd52huq zmm5, zmm13, zmm22
	vpmadd52huq zmm11, zmm15, zmm27
	add r9, 8
	sub rcx, 1
	jne 2322b
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpermq zmm31, zmm28, 147
	vpmadd52huq zmm10, zmm15, zmm31
	vpmadd52luq zmm10, zmm15, zmm23
	vpaddq zmm4, zmm4, zmm10
	vpaddq zmm5, zmm5, zmm11
	vpaddq zmm0, zmm0, zmm6
	vpaddq zmm1, zmm1, zmm7
	vpaddq zmm2, zmm2, zmm8
	vpaddq zmm3, zmm3, zmm9
	vmovdqu64 YMMWORD PTR [r11], ymm4
	vextracti64x4 YMMWORD PTR [r11+4800], zmm4, 1
	vmovdqu64 YMMWORD PTR [r11+32], ymm5
	vextracti64x4 YMMWORD PTR [r11+4832], zmm5, 1
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vextracti64x4 YMMWORD PTR [r11+4864], zmm0, 1
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vextracti64x4 YMMWORD PTR [r11+4896], zmm1, 1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vextracti64x4 YMMWORD PTR [r11+4928], zmm2, 1
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vextracti64x4 YMMWORD PTR [r11+4960], zmm3, 1
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4864], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4896]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4896], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4872]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4872], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4904]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4904], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4880]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4880], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4912]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4912], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4888]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4888], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4920]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4920], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4984], rcx
	shr rsi, 52
	mov r8, rbx
	add r8, 608
	mov r9, rbx
	add r9, 416
	mov r11, rbx
	add r11, 416
	mov r10, rbx
	mov ecx, 3
	movabs rax, 4503599627370495
	vmovq xmm30, rax
	vpermq zmm30, zmm30, 64
	vinserti64x4 zmm30, zmm30, ymm30, 1
	vmovdqu64 ymm17, YMMWORD PTR [r8]
	vinserti64x4 zmm17, zmm17, YMMWORD PTR [r8+4800], 1
	vmovdqu64 ymm18, YMMWORD PTR [r8+32]
	vinserti64x4 zmm18, zmm18, YMMWORD PTR [r8+4832], 1
	vmovdqu64 ymm19, YMMWORD PTR [r8+64]
	vinserti64x4 zmm19, zmm19, YMMWORD PTR [r8+4864], 1
	vmovdqu64 ymm20, YMMWORD PTR [r8+96]
	vinserti64x4 zmm20, zmm20, YMMWORD PTR [r8+4896], 1
	vmovdqu64 ymm21, YMMWORD PTR [r8+128]
	vinserti64x4 zmm21, zmm21, YMMWORD PTR [r8+4928], 1
	vmovdqu64 ymm22, YMMWORD PTR [r8+160]
	vinserti64x4 zmm22, zmm22, YMMWORD PTR [r8+4960], 1
	vmovdqu64 ymm24, YMMWORD PTR [r10+4416]
	vinserti64x4 zmm24, zmm24, YMMWORD PTR [r10+9216], 1
	vmovdqu64 ymm25, YMMWORD PTR [r10+4448]
	vinserti64x4 zmm25, zmm25, YMMWORD PTR [r10+9248], 1
	vmovdqu64 ymm26, YMMWORD PTR [r10+4480]
	vinserti64x4 zmm26, zmm26, YMMWORD PTR [r10+9280], 1
	vmovdqu64 ymm27, YMMWORD PTR [r10+4512]
	vinserti64x4 zmm27, zmm27, YMMWORD PTR [r10+9312], 1
	vmovdqu64 ymm28, YMMWORD PTR [r10+4544]
	vinserti64x4 zmm28, zmm28, YMMWORD PTR [r10+9344], 1
	vmovdqu64 ymm29, YMMWORD PTR [r10+4576]
	vinserti64x4 zmm29, zmm29, YMMWORD PTR [r10+9376], 1
	vpermq zmm23, zmm29, 147
	vpxorq zmm0, zmm0, zmm0
	vpxorq zmm1, zmm1, zmm1
	vpxorq zmm2, zmm2, zmm2
	vpxorq zmm3, zmm3, zmm3
	vpxorq zmm4, zmm4, zmm4
	vpxorq zmm5, zmm5, zmm5
	vpxorq zmm6, zmm6, zmm6
	vpxorq zmm7, zmm7, zmm7
	vpxorq zmm8, zmm8, zmm8
	vpxorq zmm9, zmm9, zmm9
	vpxorq zmm10, zmm10, zmm10
	vpxorq zmm11, zmm11, zmm11
	vpxorq zmm15, zmm15, zmm15
	vpbroadcastq ymm12, QWORD PTR [r9]
	vpbroadcastq ymm31, QWORD PTR [r9+4800]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
2323:
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpbroadcastq ymm12, QWORD PTR [r9+128]
	vpbroadcastq ymm31, QWORD PTR [r9+4928]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm4, zmm12, zmm17
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpaddq zmm10, zmm10, zmm4
	vpermq zmm14, zmm10, 0
	vpsrlq zmm16, zmm10, 52
	vpbroadcastq ymm13, QWORD PTR [r9+160]
	vpbroadcastq ymm31, QWORD PTR [r9+4960]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm5, zmm13, zmm17
	vpmadd52luq zmm5, zmm12, zmm18
	vpmadd52huq zmm5, zmm12, zmm17
	vpaddq zmm5, zmm5, zmm16
	vpermq zmm10, zmm10, 249
	vpandq zmm10, zmm10, zmm30
	vpxorq zmm4, zmm4, zmm4
	vpmadd52huq zmm10, zmm15, zmm28
	vpmadd52luq zmm10, zmm15, zmm29
	vpmadd52luq zmm10, zmm14, zmm28
	vpmadd52luq zmm0, zmm12, zmm19
	vpmadd52huq zmm0, zmm12, zmm18
	vpmadd52luq zmm6, zmm14, zmm24
	vpmadd52huq zmm6, zmm14, zmm23
	vpmadd52luq zmm1, zmm12, zmm20
	vpmadd52huq zmm1, zmm12, zmm19
	vpmadd52luq zmm7, zmm14, zmm25
	vpmadd52huq zmm7, zmm14, zmm24
	vpmadd52luq zmm2, zmm12, zmm21
	vpmadd52huq zmm2, zmm12, zmm20
	vpmadd52luq zmm8, zmm14, zmm26
	vpmadd52huq zmm8, zmm14, zmm25
	vpmadd52luq zmm3, zmm12, zmm22
	vpmadd52huq zmm3, zmm12, zmm21
	vpmadd52luq zmm9, zmm14, zmm27
	vpmadd52huq zmm9, zmm14, zmm26
	vpmadd52huq zmm4, zmm12, zmm22
	vpmadd52huq zmm10, zmm14, zmm27
	vpaddq zmm11, zmm11, zmm5
	vpermq zmm15, zmm11, 0
	vpsrlq zmm16, zmm11, 52
	vpbroadcastq ymm12, QWORD PTR [r9+8]
	vpbroadcastq ymm31, QWORD PTR [r9+4808]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
	vpmadd52luq zmm0, zmm13, zmm18
	vpmadd52huq zmm0, zmm13, zmm17
	vpaddq zmm0, zmm0, zmm16
	vpermq zmm11, zmm11, 249
	vpandq zmm11, zmm11, zmm30
	vpxorq zmm5, zmm5, zmm5
	vpmadd52huq zmm11, zmm14, zmm28
	vpmadd52luq zmm11, zmm14, zmm29
	vpmadd52luq zmm11, zmm15, zmm28
	vpmadd52luq zmm1, zmm13, zmm19
	vpmadd52huq zmm1, zmm13, zmm18
	vpmadd52luq zmm7, zmm15, zmm24
	vpmadd52huq zmm7, zmm15, zmm23
	vpmadd52luq zmm2, zmm13, zmm20
	vpmadd52huq zmm2, zmm13, zmm19
	vpmadd52luq zmm8, zmm15, zmm25
	vpmadd52huq zmm8, zmm15, zmm24
	vpmadd52luq zmm3, zmm13, zmm21
	vpmadd52huq zmm3, zmm13, zmm20
	vpmadd52luq zmm9, zmm15, zmm26
	vpmadd52huq zmm9, zmm15, zmm25
	vpmadd52luq zmm4, zmm13, zmm22
	vpmadd52huq zmm4, zmm13, zmm21
	vpmadd52luq zmm10, zmm15, zmm27
	vpmadd52huq zmm10, zmm15, zmm26
	vpmadd52huq zmm5, zmm13, zmm22
	vpmadd52huq zmm11, zmm15, zmm27
	add r9, 8
	sub rcx, 1
	jne 2323b
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpermq zmm31, zmm28, 147
	vpmadd52huq zmm10, zmm15, zmm31
	vpmadd52luq zmm10, zmm15, zmm23
	vpaddq zmm4, zmm4, zmm10
	vpaddq zmm5, zmm5, zmm11
	vpaddq zmm0, zmm0, zmm6
	vpaddq zmm1, zmm1, zmm7
	vpaddq zmm2, zmm2, zmm8
	vpaddq zmm3, zmm3, zmm9
	vmovdqu64 YMMWORD PTR [r11], ymm4
	vextracti64x4 YMMWORD PTR [r11+4800], zmm4, 1
	vmovdqu64 YMMWORD PTR [r11+32], ymm5
	vextracti64x4 YMMWORD PTR [r11+4832], zmm5, 1
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vextracti64x4 YMMWORD PTR [r11+4864], zmm0, 1
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vextracti64x4 YMMWORD PTR [r11+4896], zmm1, 1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vextracti64x4 YMMWORD PTR [r11+4928], zmm2, 1
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vextracti64x4 YMMWORD PTR [r11+4960], zmm3, 1
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4864], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4896]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4896], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4872]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4872], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4904]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4904], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4880]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4880], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4912]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4912], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4888]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4888], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4920]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4920], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4984], rcx
	shr rsi, 52
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4224]
	vmovdqu64 YMMWORD PTR [rbx+4608], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4256]
	vmovdqu64 YMMWORD PTR [rbx+4640], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4288]
	vmovdqu64 YMMWORD PTR [rbx+4672], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4320]
	vmovdqu64 YMMWORD PTR [rbx+4704], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4352]
	vmovdqu64 YMMWORD PTR [rbx+4736], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4384]
	vmovdqu64 YMMWORD PTR [rbx+4768], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9024]
	vmovdqu64 YMMWORD PTR [rbx+9408], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9056]
	vmovdqu64 YMMWORD PTR [rbx+9440], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9088]
	vmovdqu64 YMMWORD PTR [rbx+9472], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9120]
	vmovdqu64 YMMWORD PTR [rbx+9504], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9152]
	vmovdqu64 YMMWORD PTR [rbx+9536], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9184]
	vmovdqu64 YMMWORD PTR [rbx+9568], ymm0
	mov r8, rbx
	add r8, 224
	mov r9, rbx
	add r9, 4000
	mov r11, rbx
	add r11, 4224
	mov r10, rbx
	mov ecx, 3
	movabs rax, 4503599627370495
	vmovq xmm30, rax
	vpermq zmm30, zmm30, 64
	vinserti64x4 zmm30, zmm30, ymm30, 1
	vmovdqu64 ymm17, YMMWORD PTR [r8]
	vinserti64x4 zmm17, zmm17, YMMWORD PTR [r8+4800], 1
	vmovdqu64 ymm18, YMMWORD PTR [r8+32]
	vinserti64x4 zmm18, zmm18, YMMWORD PTR [r8+4832], 1
	vmovdqu64 ymm19, YMMWORD PTR [r8+64]
	vinserti64x4 zmm19, zmm19, YMMWORD PTR [r8+4864], 1
	vmovdqu64 ymm20, YMMWORD PTR [r8+96]
	vinserti64x4 zmm20, zmm20, YMMWORD PTR [r8+4896], 1
	vmovdqu64 ymm21, YMMWORD PTR [r8+128]
	vinserti64x4 zmm21, zmm21, YMMWORD PTR [r8+4928], 1
	vmovdqu64 ymm22, YMMWORD PTR [r8+160]
	vinserti64x4 zmm22, zmm22, YMMWORD PTR [r8+4960], 1
	vmovdqu64 ymm24, YMMWORD PTR [r10+4416]
	vinserti64x4 zmm24, zmm24, YMMWORD PTR [r10+9216], 1
	vmovdqu64 ymm25, YMMWORD PTR [r10+4448]
	vinserti64x4 zmm25, zmm25, YMMWORD PTR [r10+9248], 1
	vmovdqu64 ymm26, YMMWORD PTR [r10+4480]
	vinserti64x4 zmm26, zmm26, YMMWORD PTR [r10+9280], 1
	vmovdqu64 ymm27, YMMWORD PTR [r10+4512]
	vinserti64x4 zmm27, zmm27, YMMWORD PTR [r10+9312], 1
	vmovdqu64 ymm28, YMMWORD PTR [r10+4544]
	vinserti64x4 zmm28, zmm28, YMMWORD PTR [r10+9344], 1
	vmovdqu64 ymm29, YMMWORD PTR [r10+4576]
	vinserti64x4 zmm29, zmm29, YMMWORD PTR [r10+9376], 1
	vpermq zmm23, zmm29, 147
	vpxorq zmm0, zmm0, zmm0
	vpxorq zmm1, zmm1, zmm1
	vpxorq zmm2, zmm2, zmm2
	vpxorq zmm3, zmm3, zmm3
	vpxorq zmm4, zmm4, zmm4
	vpxorq zmm5, zmm5, zmm5
	vpxorq zmm6, zmm6, zmm6
	vpxorq zmm7, zmm7, zmm7
	vpxorq zmm8, zmm8, zmm8
	vpxorq zmm9, zmm9, zmm9
	vpxorq zmm10, zmm10, zmm10
	vpxorq zmm11, zmm11, zmm11
	vpxorq zmm15, zmm15, zmm15
	vpbroadcastq ymm12, QWORD PTR [r9]
	vpbroadcastq ymm31, QWORD PTR [r9+4800]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
2324:
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpbroadcastq ymm12, QWORD PTR [r9+128]
	vpbroadcastq ymm31, QWORD PTR [r9+4928]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm4, zmm12, zmm17
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpaddq zmm10, zmm10, zmm4
	vpermq zmm14, zmm10, 0
	vpsrlq zmm16, zmm10, 52
	vpbroadcastq ymm13, QWORD PTR [r9+160]
	vpbroadcastq ymm31, QWORD PTR [r9+4960]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm5, zmm13, zmm17
	vpmadd52luq zmm5, zmm12, zmm18
	vpmadd52huq zmm5, zmm12, zmm17
	vpaddq zmm5, zmm5, zmm16
	vpermq zmm10, zmm10, 249
	vpandq zmm10, zmm10, zmm30
	vpxorq zmm4, zmm4, zmm4
	vpmadd52huq zmm10, zmm15, zmm28
	vpmadd52luq zmm10, zmm15, zmm29
	vpmadd52luq zmm10, zmm14, zmm28
	vpmadd52luq zmm0, zmm12, zmm19
	vpmadd52huq zmm0, zmm12, zmm18
	vpmadd52luq zmm6, zmm14, zmm24
	vpmadd52huq zmm6, zmm14, zmm23
	vpmadd52luq zmm1, zmm12, zmm20
	vpmadd52huq zmm1, zmm12, zmm19
	vpmadd52luq zmm7, zmm14, zmm25
	vpmadd52huq zmm7, zmm14, zmm24
	vpmadd52luq zmm2, zmm12, zmm21
	vpmadd52huq zmm2, zmm12, zmm20
	vpmadd52luq zmm8, zmm14, zmm26
	vpmadd52huq zmm8, zmm14, zmm25
	vpmadd52luq zmm3, zmm12, zmm22
	vpmadd52huq zmm3, zmm12, zmm21
	vpmadd52luq zmm9, zmm14, zmm27
	vpmadd52huq zmm9, zmm14, zmm26
	vpmadd52huq zmm4, zmm12, zmm22
	vpmadd52huq zmm10, zmm14, zmm27
	vpaddq zmm11, zmm11, zmm5
	vpermq zmm15, zmm11, 0
	vpsrlq zmm16, zmm11, 52
	vpbroadcastq ymm12, QWORD PTR [r9+8]
	vpbroadcastq ymm31, QWORD PTR [r9+4808]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
	vpmadd52luq zmm0, zmm13, zmm18
	vpmadd52huq zmm0, zmm13, zmm17
	vpaddq zmm0, zmm0, zmm16
	vpermq zmm11, zmm11, 249
	vpandq zmm11, zmm11, zmm30
	vpxorq zmm5, zmm5, zmm5
	vpmadd52huq zmm11, zmm14, zmm28
	vpmadd52luq zmm11, zmm14, zmm29
	vpmadd52luq zmm11, zmm15, zmm28
	vpmadd52luq zmm1, zmm13, zmm19
	vpmadd52huq zmm1, zmm13, zmm18
	vpmadd52luq zmm7, zmm15, zmm24
	vpmadd52huq zmm7, zmm15, zmm23
	vpmadd52luq zmm2, zmm13, zmm20
	vpmadd52huq zmm2, zmm13, zmm19
	vpmadd52luq zmm8, zmm15, zmm25
	vpmadd52huq zmm8, zmm15, zmm24
	vpmadd52luq zmm3, zmm13, zmm21
	vpmadd52huq zmm3, zmm13, zmm20
	vpmadd52luq zmm9, zmm15, zmm26
	vpmadd52huq zmm9, zmm15, zmm25
	vpmadd52luq zmm4, zmm13, zmm22
	vpmadd52huq zmm4, zmm13, zmm21
	vpmadd52luq zmm10, zmm15, zmm27
	vpmadd52huq zmm10, zmm15, zmm26
	vpmadd52huq zmm5, zmm13, zmm22
	vpmadd52huq zmm11, zmm15, zmm27
	add r9, 8
	sub rcx, 1
	jne 2324b
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpermq zmm31, zmm28, 147
	vpmadd52huq zmm10, zmm15, zmm31
	vpmadd52luq zmm10, zmm15, zmm23
	vpaddq zmm4, zmm4, zmm10
	vpaddq zmm5, zmm5, zmm11
	vpaddq zmm0, zmm0, zmm6
	vpaddq zmm1, zmm1, zmm7
	vpaddq zmm2, zmm2, zmm8
	vpaddq zmm3, zmm3, zmm9
	vmovdqu64 YMMWORD PTR [r11], ymm4
	vextracti64x4 YMMWORD PTR [r11+4800], zmm4, 1
	vmovdqu64 YMMWORD PTR [r11+32], ymm5
	vextracti64x4 YMMWORD PTR [r11+4832], zmm5, 1
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vextracti64x4 YMMWORD PTR [r11+4864], zmm0, 1
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vextracti64x4 YMMWORD PTR [r11+4896], zmm1, 1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vextracti64x4 YMMWORD PTR [r11+4928], zmm2, 1
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vextracti64x4 YMMWORD PTR [r11+4960], zmm3, 1
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4864], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4896]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4896], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4872]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4872], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4904]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4904], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4880]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4880], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4912]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4912], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4888]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4888], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4920]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4920], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4984], rcx
	shr rsi, 52
	mov r13d, 800
2325:
	cmp r13, 1184
	jb 2326f
	mov r8, rbx
	add r8, r13
	sub r8, 192
	mov r9, rbx
	add r9, 416
	mov r11, rbx
	add r11, r13
	jmp 2327f
2326:
	mov r8, rbx
	add r8, r13
	sub r8, 576
	mov r9, rbx
	add r9, 4000
	mov r11, r8
2327:
	mov r10, rbx
	mov ecx, 3
	movabs rax, 4503599627370495
	vmovq xmm30, rax
	vpermq zmm30, zmm30, 64
	vinserti64x4 zmm30, zmm30, ymm30, 1
	vmovdqu64 ymm17, YMMWORD PTR [r8]
	vinserti64x4 zmm17, zmm17, YMMWORD PTR [r8+4800], 1
	vmovdqu64 ymm18, YMMWORD PTR [r8+32]
	vinserti64x4 zmm18, zmm18, YMMWORD PTR [r8+4832], 1
	vmovdqu64 ymm19, YMMWORD PTR [r8+64]
	vinserti64x4 zmm19, zmm19, YMMWORD PTR [r8+4864], 1
	vmovdqu64 ymm20, YMMWORD PTR [r8+96]
	vinserti64x4 zmm20, zmm20, YMMWORD PTR [r8+4896], 1
	vmovdqu64 ymm21, YMMWORD PTR [r8+128]
	vinserti64x4 zmm21, zmm21, YMMWORD PTR [r8+4928], 1
	vmovdqu64 ymm22, YMMWORD PTR [r8+160]
	vinserti64x4 zmm22, zmm22, YMMWORD PTR [r8+4960], 1
	vmovdqu64 ymm24, YMMWORD PTR [r10+4416]
	vinserti64x4 zmm24, zmm24, YMMWORD PTR [r10+9216], 1
	vmovdqu64 ymm25, YMMWORD PTR [r10+4448]
	vinserti64x4 zmm25, zmm25, YMMWORD PTR [r10+9248], 1
	vmovdqu64 ymm26, YMMWORD PTR [r10+4480]
	vinserti64x4 zmm26, zmm26, YMMWORD PTR [r10+9280], 1
	vmovdqu64 ymm27, YMMWORD PTR [r10+4512]
	vinserti64x4 zmm27, zmm27, YMMWORD PTR [r10+9312], 1
	vmovdqu64 ymm28, YMMWORD PTR [r10+4544]
	vinserti64x4 zmm28, zmm28, YMMWORD PTR [r10+9344], 1
	vmovdqu64 ymm29, YMMWORD PTR [r10+4576]
	vinserti64x4 zmm29, zmm29, YMMWORD PTR [r10+9376], 1
	vpermq zmm23, zmm29, 147
	vpxorq zmm0, zmm0, zmm0
	vpxorq zmm1, zmm1, zmm1
	vpxorq zmm2, zmm2, zmm2
	vpxorq zmm3, zmm3, zmm3
	vpxorq zmm4, zmm4, zmm4
	vpxorq zmm5, zmm5, zmm5
	vpxorq zmm6, zmm6, zmm6
	vpxorq zmm7, zmm7, zmm7
	vpxorq zmm8, zmm8, zmm8
	vpxorq zmm9, zmm9, zmm9
	vpxorq zmm10, zmm10, zmm10
	vpxorq zmm11, zmm11, zmm11
	vpxorq zmm15, zmm15, zmm15
	vpbroadcastq ymm12, QWORD PTR [r9]
	vpbroadcastq ymm31, QWORD PTR [r9+4800]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
2328:
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpbroadcastq ymm12, QWORD PTR [r9+128]
	vpbroadcastq ymm31, QWORD PTR [r9+4928]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm4, zmm12, zmm17
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpaddq zmm10, zmm10, zmm4
	vpermq zmm14, zmm10, 0
	vpsrlq zmm16, zmm10, 52
	vpbroadcastq ymm13, QWORD PTR [r9+160]
	vpbroadcastq ymm31, QWORD PTR [r9+4960]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm5, zmm13, zmm17
	vpmadd52luq zmm5, zmm12, zmm18
	vpmadd52huq zmm5, zmm12, zmm17
	vpaddq zmm5, zmm5, zmm16
	vpermq zmm10, zmm10, 249
	vpandq zmm10, zmm10, zmm30
	vpxorq zmm4, zmm4, zmm4
	vpmadd52huq zmm10, zmm15, zmm28
	vpmadd52luq zmm10, zmm15, zmm29
	vpmadd52luq zmm10, zmm14, zmm28
	vpmadd52luq zmm0, zmm12, zmm19
	vpmadd52huq zmm0, zmm12, zmm18
	vpmadd52luq zmm6, zmm14, zmm24
	vpmadd52huq zmm6, zmm14, zmm23
	vpmadd52luq zmm1, zmm12, zmm20
	vpmadd52huq zmm1, zmm12, zmm19
	vpmadd52luq zmm7, zmm14, zmm25
	vpmadd52huq zmm7, zmm14, zmm24
	vpmadd52luq zmm2, zmm12, zmm21
	vpmadd52huq zmm2, zmm12, zmm20
	vpmadd52luq zmm8, zmm14, zmm26
	vpmadd52huq zmm8, zmm14, zmm25
	vpmadd52luq zmm3, zmm12, zmm22
	vpmadd52huq zmm3, zmm12, zmm21
	vpmadd52luq zmm9, zmm14, zmm27
	vpmadd52huq zmm9, zmm14, zmm26
	vpmadd52huq zmm4, zmm12, zmm22
	vpmadd52huq zmm10, zmm14, zmm27
	vpaddq zmm11, zmm11, zmm5
	vpermq zmm15, zmm11, 0
	vpsrlq zmm16, zmm11, 52
	vpbroadcastq ymm12, QWORD PTR [r9+8]
	vpbroadcastq ymm31, QWORD PTR [r9+4808]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
	vpmadd52luq zmm0, zmm13, zmm18
	vpmadd52huq zmm0, zmm13, zmm17
	vpaddq zmm0, zmm0, zmm16
	vpermq zmm11, zmm11, 249
	vpandq zmm11, zmm11, zmm30
	vpxorq zmm5, zmm5, zmm5
	vpmadd52huq zmm11, zmm14, zmm28
	vpmadd52luq zmm11, zmm14, zmm29
	vpmadd52luq zmm11, zmm15, zmm28
	vpmadd52luq zmm1, zmm13, zmm19
	vpmadd52huq zmm1, zmm13, zmm18
	vpmadd52luq zmm7, zmm15, zmm24
	vpmadd52huq zmm7, zmm15, zmm23
	vpmadd52luq zmm2, zmm13, zmm20
	vpmadd52huq zmm2, zmm13, zmm19
	vpmadd52luq zmm8, zmm15, zmm25
	vpmadd52huq zmm8, zmm15, zmm24
	vpmadd52luq zmm3, zmm13, zmm21
	vpmadd52huq zmm3, zmm13, zmm20
	vpmadd52luq zmm9, zmm15, zmm26
	vpmadd52huq zmm9, zmm15, zmm25
	vpmadd52luq zmm4, zmm13, zmm22
	vpmadd52huq zmm4, zmm13, zmm21
	vpmadd52luq zmm10, zmm15, zmm27
	vpmadd52huq zmm10, zmm15, zmm26
	vpmadd52huq zmm5, zmm13, zmm22
	vpmadd52huq zmm11, zmm15, zmm27
	add r9, 8
	sub rcx, 1
	jne 2328b
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpermq zmm31, zmm28, 147
	vpmadd52huq zmm10, zmm15, zmm31
	vpmadd52luq zmm10, zmm15, zmm23
	vpaddq zmm4, zmm4, zmm10
	vpaddq zmm5, zmm5, zmm11
	vpaddq zmm0, zmm0, zmm6
	vpaddq zmm1, zmm1, zmm7
	vpaddq zmm2, zmm2, zmm8
	vpaddq zmm3, zmm3, zmm9
	vmovdqu64 YMMWORD PTR [r11], ymm4
	vextracti64x4 YMMWORD PTR [r11+4800], zmm4, 1
	vmovdqu64 YMMWORD PTR [r11+32], ymm5
	vextracti64x4 YMMWORD PTR [r11+4832], zmm5, 1
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vextracti64x4 YMMWORD PTR [r11+4864], zmm0, 1
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vextracti64x4 YMMWORD PTR [r11+4896], zmm1, 1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vextracti64x4 YMMWORD PTR [r11+4928], zmm2, 1
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vextracti64x4 YMMWORD PTR [r11+4960], zmm3, 1
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4864], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4896]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4896], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4872]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4872], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4904]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4904], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4880]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4880], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4912]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4912], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4888]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4888], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4920]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4920], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4984], rcx
	shr rsi, 52
	cmp r13, 992
	je 2329f
	jmp 2330f
2329:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+224]
	vmovdqu64 YMMWORD PTR [rbx+800], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+256]
	vmovdqu64 YMMWORD PTR [rbx+832], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+288]
	vmovdqu64 YMMWORD PTR [rbx+864], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+320]
	vmovdqu64 YMMWORD PTR [rbx+896], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+352]
	vmovdqu64 YMMWORD PTR [rbx+928], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+384]
	vmovdqu64 YMMWORD PTR [rbx+960], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5024]
	vmovdqu64 YMMWORD PTR [rbx+5600], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5056]
	vmovdqu64 YMMWORD PTR [rbx+5632], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5088]
	vmovdqu64 YMMWORD PTR [rbx+5664], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5120]
	vmovdqu64 YMMWORD PTR [rbx+5696], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5152]
	vmovdqu64 YMMWORD PTR [rbx+5728], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5184]
	vmovdqu64 YMMWORD PTR [rbx+5760], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+416]
	vmovdqu64 YMMWORD PTR [rbx+992], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+448]
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+480]
	vmovdqu64 YMMWORD PTR [rbx+1056], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+512]
	vmovdqu64 YMMWORD PTR [rbx+1088], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+544]
	vmovdqu64 YMMWORD PTR [rbx+1120], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+576]
	vmovdqu64 YMMWORD PTR [rbx+1152], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5216]
	vmovdqu64 YMMWORD PTR [rbx+5792], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5248]
	vmovdqu64 YMMWORD PTR [rbx+5824], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5280]
	vmovdqu64 YMMWORD PTR [rbx+5856], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5312]
	vmovdqu64 YMMWORD PTR [rbx+5888], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5344]
	vmovdqu64 YMMWORD PTR [rbx+5920], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+5376]
	vmovdqu64 YMMWORD PTR [rbx+5952], ymm0
2330:
	add r13, 192
	cmp r13, 3872
	jne 2325b
	mov r13d, 0
2331:
	cmp r13, 256
	je 2332f
	mov r8, r13
	shr r8, 1
	mov rdx, r13
	and rdx, 1
	sub rdx, 1
	movzx eax, BYTE PTR [rbx+r8*1+3872]
	movzx esi, BYTE PTR [rbx+r8*1+8672]
	mov rcx, rax
	shr rcx, 4
	and rax, 15
	xor rcx, rax
	and rcx, rdx
	xor rax, rcx
	mov QWORD PTR [rbx+4192], rax
	mov rcx, rsi
	shr rcx, 4
	and rsi, 15
	xor rcx, rsi
	and rcx, rdx
	xor rsi, rcx
	mov QWORD PTR [rbx+8992], rsi
	mov r8, rbx
	add r8, 800
	mov rdx, QWORD PTR [rbx+4192]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
2334:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm6, rax
	vpbroadcastq ymm6, xmm6
	vmovdqu64 ymm7, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm7, ymm6, 248
	add r8, 192
	add rcx, 1
	cmp rcx, 16
	jne 2334b
	vmovdqu64 YMMWORD PTR [rbx+608], ymm0
	vmovdqu64 YMMWORD PTR [rbx+640], ymm1
	vmovdqu64 YMMWORD PTR [rbx+672], ymm2
	vmovdqu64 YMMWORD PTR [rbx+704], ymm3
	vmovdqu64 YMMWORD PTR [rbx+736], ymm4
	vmovdqu64 YMMWORD PTR [rbx+768], ymm5
	mov r8, rbx
	add r8, 5600
	mov rdx, QWORD PTR [rbx+8992]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
2335:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm6, rax
	vpbroadcastq ymm6, xmm6
	vmovdqu64 ymm7, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm7, ymm6, 248
	vmovdqu64 ymm7, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm7, ymm6, 248
	add r8, 192
	add rcx, 1
	cmp rcx, 16
	jne 2335b
	vmovdqu64 YMMWORD PTR [rbx+5408], ymm0
	vmovdqu64 YMMWORD PTR [rbx+5440], ymm1
	vmovdqu64 YMMWORD PTR [rbx+5472], ymm2
	vmovdqu64 YMMWORD PTR [rbx+5504], ymm3
	vmovdqu64 YMMWORD PTR [rbx+5536], ymm4
	vmovdqu64 YMMWORD PTR [rbx+5568], ymm5
	mov r15d, 5
	jmp 2333f
2332:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4224]
	vmovdqu64 YMMWORD PTR [rbx+608], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4256]
	vmovdqu64 YMMWORD PTR [rbx+640], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4288]
	vmovdqu64 YMMWORD PTR [rbx+672], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4320]
	vmovdqu64 YMMWORD PTR [rbx+704], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4352]
	vmovdqu64 YMMWORD PTR [rbx+736], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+4384]
	vmovdqu64 YMMWORD PTR [rbx+768], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9024]
	vmovdqu64 YMMWORD PTR [rbx+5408], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9056]
	vmovdqu64 YMMWORD PTR [rbx+5440], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9088]
	vmovdqu64 YMMWORD PTR [rbx+5472], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9120]
	vmovdqu64 YMMWORD PTR [rbx+5504], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9152]
	vmovdqu64 YMMWORD PTR [rbx+5536], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+9184]
	vmovdqu64 YMMWORD PTR [rbx+5568], ymm0
	mov r15d, 1
2333:
2336:
	cmp r15, 1
	je 2337f
	mov r8, rbx
	add r8, 224
	mov r9, rbx
	add r9, 224
	mov r11, rbx
	add r11, 224
	jmp 2338f
2337:
	mov r8, rbx
	add r8, 224
	mov r9, rbx
	add r9, 608
	mov r11, rbx
	add r11, 224
2338:
	mov r10, rbx
	mov ecx, 3
	movabs rax, 4503599627370495
	vmovq xmm30, rax
	vpermq zmm30, zmm30, 64
	vinserti64x4 zmm30, zmm30, ymm30, 1
	vmovdqu64 ymm17, YMMWORD PTR [r8]
	vinserti64x4 zmm17, zmm17, YMMWORD PTR [r8+4800], 1
	vmovdqu64 ymm18, YMMWORD PTR [r8+32]
	vinserti64x4 zmm18, zmm18, YMMWORD PTR [r8+4832], 1
	vmovdqu64 ymm19, YMMWORD PTR [r8+64]
	vinserti64x4 zmm19, zmm19, YMMWORD PTR [r8+4864], 1
	vmovdqu64 ymm20, YMMWORD PTR [r8+96]
	vinserti64x4 zmm20, zmm20, YMMWORD PTR [r8+4896], 1
	vmovdqu64 ymm21, YMMWORD PTR [r8+128]
	vinserti64x4 zmm21, zmm21, YMMWORD PTR [r8+4928], 1
	vmovdqu64 ymm22, YMMWORD PTR [r8+160]
	vinserti64x4 zmm22, zmm22, YMMWORD PTR [r8+4960], 1
	vmovdqu64 ymm24, YMMWORD PTR [r10+4416]
	vinserti64x4 zmm24, zmm24, YMMWORD PTR [r10+9216], 1
	vmovdqu64 ymm25, YMMWORD PTR [r10+4448]
	vinserti64x4 zmm25, zmm25, YMMWORD PTR [r10+9248], 1
	vmovdqu64 ymm26, YMMWORD PTR [r10+4480]
	vinserti64x4 zmm26, zmm26, YMMWORD PTR [r10+9280], 1
	vmovdqu64 ymm27, YMMWORD PTR [r10+4512]
	vinserti64x4 zmm27, zmm27, YMMWORD PTR [r10+9312], 1
	vmovdqu64 ymm28, YMMWORD PTR [r10+4544]
	vinserti64x4 zmm28, zmm28, YMMWORD PTR [r10+9344], 1
	vmovdqu64 ymm29, YMMWORD PTR [r10+4576]
	vinserti64x4 zmm29, zmm29, YMMWORD PTR [r10+9376], 1
	vpermq zmm23, zmm29, 147
	vpxorq zmm0, zmm0, zmm0
	vpxorq zmm1, zmm1, zmm1
	vpxorq zmm2, zmm2, zmm2
	vpxorq zmm3, zmm3, zmm3
	vpxorq zmm4, zmm4, zmm4
	vpxorq zmm5, zmm5, zmm5
	vpxorq zmm6, zmm6, zmm6
	vpxorq zmm7, zmm7, zmm7
	vpxorq zmm8, zmm8, zmm8
	vpxorq zmm9, zmm9, zmm9
	vpxorq zmm10, zmm10, zmm10
	vpxorq zmm11, zmm11, zmm11
	vpxorq zmm15, zmm15, zmm15
	vpbroadcastq ymm12, QWORD PTR [r9]
	vpbroadcastq ymm31, QWORD PTR [r9+4800]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
2339:
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpbroadcastq ymm12, QWORD PTR [r9+128]
	vpbroadcastq ymm31, QWORD PTR [r9+4928]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm4, zmm12, zmm17
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpaddq zmm10, zmm10, zmm4
	vpermq zmm14, zmm10, 0
	vpsrlq zmm16, zmm10, 52
	vpbroadcastq ymm13, QWORD PTR [r9+160]
	vpbroadcastq ymm31, QWORD PTR [r9+4960]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm5, zmm13, zmm17
	vpmadd52luq zmm5, zmm12, zmm18
	vpmadd52huq zmm5, zmm12, zmm17
	vpaddq zmm5, zmm5, zmm16
	vpermq zmm10, zmm10, 249
	vpandq zmm10, zmm10, zmm30
	vpxorq zmm4, zmm4, zmm4
	vpmadd52huq zmm10, zmm15, zmm28
	vpmadd52luq zmm10, zmm15, zmm29
	vpmadd52luq zmm10, zmm14, zmm28
	vpmadd52luq zmm0, zmm12, zmm19
	vpmadd52huq zmm0, zmm12, zmm18
	vpmadd52luq zmm6, zmm14, zmm24
	vpmadd52huq zmm6, zmm14, zmm23
	vpmadd52luq zmm1, zmm12, zmm20
	vpmadd52huq zmm1, zmm12, zmm19
	vpmadd52luq zmm7, zmm14, zmm25
	vpmadd52huq zmm7, zmm14, zmm24
	vpmadd52luq zmm2, zmm12, zmm21
	vpmadd52huq zmm2, zmm12, zmm20
	vpmadd52luq zmm8, zmm14, zmm26
	vpmadd52huq zmm8, zmm14, zmm25
	vpmadd52luq zmm3, zmm12, zmm22
	vpmadd52huq zmm3, zmm12, zmm21
	vpmadd52luq zmm9, zmm14, zmm27
	vpmadd52huq zmm9, zmm14, zmm26
	vpmadd52huq zmm4, zmm12, zmm22
	vpmadd52huq zmm10, zmm14, zmm27
	vpaddq zmm11, zmm11, zmm5
	vpermq zmm15, zmm11, 0
	vpsrlq zmm16, zmm11, 52
	vpbroadcastq ymm12, QWORD PTR [r9+8]
	vpbroadcastq ymm31, QWORD PTR [r9+4808]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm0, zmm12, zmm17
	vpmadd52luq zmm0, zmm13, zmm18
	vpmadd52huq zmm0, zmm13, zmm17
	vpaddq zmm0, zmm0, zmm16
	vpermq zmm11, zmm11, 249
	vpandq zmm11, zmm11, zmm30
	vpxorq zmm5, zmm5, zmm5
	vpmadd52huq zmm11, zmm14, zmm28
	vpmadd52luq zmm11, zmm14, zmm29
	vpmadd52luq zmm11, zmm15, zmm28
	vpmadd52luq zmm1, zmm13, zmm19
	vpmadd52huq zmm1, zmm13, zmm18
	vpmadd52luq zmm7, zmm15, zmm24
	vpmadd52huq zmm7, zmm15, zmm23
	vpmadd52luq zmm2, zmm13, zmm20
	vpmadd52huq zmm2, zmm13, zmm19
	vpmadd52luq zmm8, zmm15, zmm25
	vpmadd52huq zmm8, zmm15, zmm24
	vpmadd52luq zmm3, zmm13, zmm21
	vpmadd52huq zmm3, zmm13, zmm20
	vpmadd52luq zmm9, zmm15, zmm26
	vpmadd52huq zmm9, zmm15, zmm25
	vpmadd52luq zmm4, zmm13, zmm22
	vpmadd52huq zmm4, zmm13, zmm21
	vpmadd52luq zmm10, zmm15, zmm27
	vpmadd52huq zmm10, zmm15, zmm26
	vpmadd52huq zmm5, zmm13, zmm22
	vpmadd52huq zmm11, zmm15, zmm27
	add r9, 8
	sub rcx, 1
	jne 2339b
	vpaddq zmm6, zmm6, zmm0
	vpermq zmm14, zmm6, 0
	vpsrlq zmm16, zmm6, 52
	vpbroadcastq ymm13, QWORD PTR [r9+32]
	vpbroadcastq ymm31, QWORD PTR [r9+4832]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm1, zmm13, zmm17
	vpmadd52luq zmm1, zmm12, zmm18
	vpmadd52huq zmm1, zmm12, zmm17
	vpaddq zmm1, zmm1, zmm16
	vpermq zmm6, zmm6, 249
	vpandq zmm6, zmm6, zmm30
	vpxorq zmm0, zmm0, zmm0
	vpmadd52huq zmm6, zmm15, zmm28
	vpmadd52luq zmm6, zmm15, zmm29
	vpmadd52luq zmm6, zmm14, zmm28
	vpmadd52luq zmm2, zmm12, zmm19
	vpmadd52huq zmm2, zmm12, zmm18
	vpmadd52luq zmm8, zmm14, zmm24
	vpmadd52huq zmm8, zmm14, zmm23
	vpmadd52luq zmm3, zmm12, zmm20
	vpmadd52huq zmm3, zmm12, zmm19
	vpmadd52luq zmm9, zmm14, zmm25
	vpmadd52huq zmm9, zmm14, zmm24
	vpmadd52luq zmm4, zmm12, zmm21
	vpmadd52huq zmm4, zmm12, zmm20
	vpmadd52luq zmm10, zmm14, zmm26
	vpmadd52huq zmm10, zmm14, zmm25
	vpmadd52luq zmm5, zmm12, zmm22
	vpmadd52huq zmm5, zmm12, zmm21
	vpmadd52luq zmm11, zmm14, zmm27
	vpmadd52huq zmm11, zmm14, zmm26
	vpmadd52huq zmm0, zmm12, zmm22
	vpmadd52huq zmm6, zmm14, zmm27
	vpaddq zmm7, zmm7, zmm1
	vpermq zmm15, zmm7, 0
	vpsrlq zmm16, zmm7, 52
	vpbroadcastq ymm12, QWORD PTR [r9+64]
	vpbroadcastq ymm31, QWORD PTR [r9+4864]
	vinserti64x4 zmm12, zmm12, ymm31, 1
	vpmadd52luq zmm2, zmm12, zmm17
	vpmadd52luq zmm2, zmm13, zmm18
	vpmadd52huq zmm2, zmm13, zmm17
	vpaddq zmm2, zmm2, zmm16
	vpermq zmm7, zmm7, 249
	vpandq zmm7, zmm7, zmm30
	vpxorq zmm1, zmm1, zmm1
	vpmadd52huq zmm7, zmm14, zmm28
	vpmadd52luq zmm7, zmm14, zmm29
	vpmadd52luq zmm7, zmm15, zmm28
	vpmadd52luq zmm3, zmm13, zmm19
	vpmadd52huq zmm3, zmm13, zmm18
	vpmadd52luq zmm9, zmm15, zmm24
	vpmadd52huq zmm9, zmm15, zmm23
	vpmadd52luq zmm4, zmm13, zmm20
	vpmadd52huq zmm4, zmm13, zmm19
	vpmadd52luq zmm10, zmm15, zmm25
	vpmadd52huq zmm10, zmm15, zmm24
	vpmadd52luq zmm5, zmm13, zmm21
	vpmadd52huq zmm5, zmm13, zmm20
	vpmadd52luq zmm11, zmm15, zmm26
	vpmadd52huq zmm11, zmm15, zmm25
	vpmadd52luq zmm0, zmm13, zmm22
	vpmadd52huq zmm0, zmm13, zmm21
	vpmadd52luq zmm6, zmm15, zmm27
	vpmadd52huq zmm6, zmm15, zmm26
	vpmadd52huq zmm1, zmm13, zmm22
	vpmadd52huq zmm7, zmm15, zmm27
	vpaddq zmm8, zmm8, zmm2
	vpermq zmm14, zmm8, 0
	vpsrlq zmm16, zmm8, 52
	vpbroadcastq ymm13, QWORD PTR [r9+96]
	vpbroadcastq ymm31, QWORD PTR [r9+4896]
	vinserti64x4 zmm13, zmm13, ymm31, 1
	vpmadd52luq zmm3, zmm13, zmm17
	vpmadd52luq zmm3, zmm12, zmm18
	vpmadd52huq zmm3, zmm12, zmm17
	vpaddq zmm3, zmm3, zmm16
	vpermq zmm8, zmm8, 249
	vpandq zmm8, zmm8, zmm30
	vpxorq zmm2, zmm2, zmm2
	vpmadd52huq zmm8, zmm15, zmm28
	vpmadd52luq zmm8, zmm15, zmm29
	vpmadd52luq zmm8, zmm14, zmm28
	vpmadd52luq zmm4, zmm12, zmm19
	vpmadd52huq zmm4, zmm12, zmm18
	vpmadd52luq zmm10, zmm14, zmm24
	vpmadd52huq zmm10, zmm14, zmm23
	vpmadd52luq zmm5, zmm12, zmm20
	vpmadd52huq zmm5, zmm12, zmm19
	vpmadd52luq zmm11, zmm14, zmm25
	vpmadd52huq zmm11, zmm14, zmm24
	vpmadd52luq zmm0, zmm12, zmm21
	vpmadd52huq zmm0, zmm12, zmm20
	vpmadd52luq zmm6, zmm14, zmm26
	vpmadd52huq zmm6, zmm14, zmm25
	vpmadd52luq zmm1, zmm12, zmm22
	vpmadd52huq zmm1, zmm12, zmm21
	vpmadd52luq zmm7, zmm14, zmm27
	vpmadd52huq zmm7, zmm14, zmm26
	vpmadd52huq zmm2, zmm12, zmm22
	vpmadd52huq zmm8, zmm14, zmm27
	vpaddq zmm9, zmm9, zmm3
	vpermq zmm15, zmm9, 0
	vpsrlq zmm16, zmm9, 52
	vpmadd52luq zmm4, zmm13, zmm18
	vpmadd52huq zmm4, zmm13, zmm17
	vpaddq zmm4, zmm4, zmm16
	vpermq zmm9, zmm9, 249
	vpandq zmm9, zmm9, zmm30
	vpxorq zmm3, zmm3, zmm3
	vpmadd52huq zmm9, zmm14, zmm28
	vpmadd52luq zmm9, zmm14, zmm29
	vpmadd52luq zmm9, zmm15, zmm28
	vpmadd52luq zmm5, zmm13, zmm19
	vpmadd52huq zmm5, zmm13, zmm18
	vpmadd52luq zmm11, zmm15, zmm24
	vpmadd52huq zmm11, zmm15, zmm23
	vpmadd52luq zmm0, zmm13, zmm20
	vpmadd52huq zmm0, zmm13, zmm19
	vpmadd52luq zmm6, zmm15, zmm25
	vpmadd52huq zmm6, zmm15, zmm24
	vpmadd52luq zmm1, zmm13, zmm21
	vpmadd52huq zmm1, zmm13, zmm20
	vpmadd52luq zmm7, zmm15, zmm26
	vpmadd52huq zmm7, zmm15, zmm25
	vpmadd52luq zmm2, zmm13, zmm22
	vpmadd52huq zmm2, zmm13, zmm21
	vpmadd52luq zmm8, zmm15, zmm27
	vpmadd52huq zmm8, zmm15, zmm26
	vpmadd52huq zmm3, zmm13, zmm22
	vpmadd52huq zmm9, zmm15, zmm27
	vpermq zmm31, zmm28, 147
	vpmadd52huq zmm10, zmm15, zmm31
	vpmadd52luq zmm10, zmm15, zmm23
	vpaddq zmm4, zmm4, zmm10
	vpaddq zmm5, zmm5, zmm11
	vpaddq zmm0, zmm0, zmm6
	vpaddq zmm1, zmm1, zmm7
	vpaddq zmm2, zmm2, zmm8
	vpaddq zmm3, zmm3, zmm9
	vmovdqu64 YMMWORD PTR [r11], ymm4
	vextracti64x4 YMMWORD PTR [r11+4800], zmm4, 1
	vmovdqu64 YMMWORD PTR [r11+32], ymm5
	vextracti64x4 YMMWORD PTR [r11+4832], zmm5, 1
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vextracti64x4 YMMWORD PTR [r11+4864], zmm0, 1
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vextracti64x4 YMMWORD PTR [r11+4896], zmm1, 1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vextracti64x4 YMMWORD PTR [r11+4928], zmm2, 1
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vextracti64x4 YMMWORD PTR [r11+4960], zmm3, 1
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4864], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4896]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4896], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4872]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4872], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4904]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4904], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4880]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4880], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4912]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4912], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4888]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4888], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4920]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4920], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4984], rcx
	shr rsi, 52
	sub r15, 1
	jne 2336b
	add r13, 1
	cmp r13, 257
	jne 2331b
	mov r8, rbx
	add r8, 224
	mov r9, rbx
	add r9, 4608
	mov r11, rbx
	add r11, 224
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
2340:
	mov rax, QWORD PTR [r9]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4800]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm0, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm6, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm0, 52
	vmovq xmm17, xmm17
	vpaddq ymm1, ymm1, ymm17
	valignq ymm0, ymm16, ymm0, 1
	vpsrlq ymm17, ymm6, 52
	vmovq xmm17, xmm17
	vpaddq ymm7, ymm7, ymm17
	valignq ymm6, ymm16, ymm6, 1
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4832]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm1, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm7, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm1, 52
	vmovq xmm17, xmm17
	vpaddq ymm2, ymm2, ymm17
	valignq ymm1, ymm16, ymm1, 1
	vpsrlq ymm17, ymm7, 52
	vmovq xmm17, xmm17
	vpaddq ymm8, ymm8, ymm17
	valignq ymm7, ymm16, ymm7, 1
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4864]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm2, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm8, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm2, 52
	vmovq xmm17, xmm17
	vpaddq ymm3, ymm3, ymm17
	valignq ymm2, ymm16, ymm2, 1
	vpsrlq ymm17, ymm8, 52
	vmovq xmm17, xmm17
	vpaddq ymm9, ymm9, ymm17
	valignq ymm8, ymm16, ymm8, 1
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4896]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm3, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm9, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm3, 52
	vmovq xmm17, xmm17
	vpaddq ymm4, ymm4, ymm17
	valignq ymm3, ymm16, ymm3, 1
	vpsrlq ymm17, ymm9, 52
	vmovq xmm17, xmm17
	vpaddq ymm10, ymm10, ymm17
	valignq ymm9, ymm16, ymm9, 1
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4928]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm4, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm4, 52
	vmovq xmm17, xmm17
	vpaddq ymm5, ymm5, ymm17
	valignq ymm4, ymm16, ymm4, 1
	vpsrlq ymm17, ymm10, 52
	vmovq xmm17, xmm17
	vpaddq ymm11, ymm11, ymm17
	valignq ymm10, ymm16, ymm10, 1
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4960]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm5, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm5, 52
	vmovq xmm17, xmm17
	vpaddq ymm0, ymm0, ymm17
	valignq ymm5, ymm16, ymm5, 1
	vpsrlq ymm17, ymm11, 52
	vmovq xmm17, xmm17
	vpaddq ymm6, ymm6, ymm17
	valignq ymm11, ymm16, ymm11, 1
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4960]
	add r9, 8
	sub rcx, 1
	jne 2340b
	mov rax, QWORD PTR [r9]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4800]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm0, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm6, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm0, 52
	vmovq xmm17, xmm17
	vpaddq ymm1, ymm1, ymm17
	valignq ymm0, ymm16, ymm0, 1
	vpsrlq ymm17, ymm6, 52
	vmovq xmm17, xmm17
	vpaddq ymm7, ymm7, ymm17
	valignq ymm6, ymm16, ymm6, 1
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4832]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm1, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm7, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm1, 52
	vmovq xmm17, xmm17
	vpaddq ymm2, ymm2, ymm17
	valignq ymm1, ymm16, ymm1, 1
	vpsrlq ymm17, ymm7, 52
	vmovq xmm17, xmm17
	vpaddq ymm8, ymm8, ymm17
	valignq ymm7, ymm16, ymm7, 1
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4864]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm2, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm8, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm2, 52
	vmovq xmm17, xmm17
	vpaddq ymm3, ymm3, ymm17
	valignq ymm2, ymm16, ymm2, 1
	vpsrlq ymm17, ymm8, 52
	vmovq xmm17, xmm17
	vpaddq ymm9, ymm9, ymm17
	valignq ymm8, ymm16, ymm8, 1
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4960]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm12, rax
	vpbroadcastq ymm12, xmm12
	mov rax, QWORD PTR [r9+4896]
	vmovq xmm13, rax
	vpbroadcastq ymm13, xmm13
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm10, ymm13, YMMWORD PTR [r8+4832]
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm3, YMMWORD PTR [r10+192]
	vpbroadcastq ymm14, xmm17
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm9, YMMWORD PTR [r10+4992]
	vpbroadcastq ymm15, xmm17
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm14, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm14, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm13, YMMWORD PTR [r8+4800]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r10+4832]
	vpsrlq ymm17, ymm3, 52
	vmovq xmm17, xmm17
	vpaddq ymm4, ymm4, ymm17
	valignq ymm3, ymm16, ymm3, 1
	vpsrlq ymm17, ymm9, 52
	vmovq xmm17, xmm17
	vpaddq ymm10, ymm10, ymm17
	valignq ymm9, ymm16, ymm9, 1
	vpmadd52huq ymm4, ymm14, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+4800]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm14, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm14, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm14, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm14, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm14, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm14, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm14, YMMWORD PTR [r10+128]
	vpmadd52luq ymm11, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52huq ymm11, ymm13, YMMWORD PTR [r8+4832]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+4832]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r8+4864]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r10+4864]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r8+4896]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+4896]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r8+4928]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+4960]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+4928]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm14, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r8+4960]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r10+4960]
	vmovdqu64 YMMWORD PTR [r11], ymm4
	vmovdqu64 YMMWORD PTR [r11+32], ymm5
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	vmovdqu64 YMMWORD PTR [r11+4800], ymm10
	vmovdqu64 YMMWORD PTR [r11+4832], ymm11
	vmovdqu64 YMMWORD PTR [r11+4864], ymm6
	vmovdqu64 YMMWORD PTR [r11+4896], ymm7
	vmovdqu64 YMMWORD PTR [r11+4928], ymm8
	vmovdqu64 YMMWORD PTR [r11+4960], ymm9
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4800]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4800], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4832]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4832], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4864]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4864], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4896]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4896], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4808]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4808], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4840]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4840], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4872]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4872], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4904]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4904], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4816]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4816], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4848]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4848], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4880]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4880], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4912]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4912], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4824]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4824], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4856]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4856], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4888]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4888], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4920]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4920], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+4984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+4984], rcx
	shr rsi, 52
	lfence
	ldmxcsr DWORD PTR [rbx+9600]
	vzeroupper
	mov r11, QWORD PTR [rdi+232]
	add r11, 5024
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
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+8]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+168]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+176]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2341:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2341b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2342:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2342b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rdi+232]
	add r11, 224
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
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+8]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+168]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+176]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2343:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2343b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2344:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2344b
	mov rdi, QWORD PTR [rdi+128]
2185:
	mov rdi, QWORD PTR [rdi+232]
	mov rsi, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rsi, rax
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2345:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2345b
	mov rax, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rax+176]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2346:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2346b
	mov rax, r15
	xor rax, -1
	and rax, 1
	or rax, QWORD PTR [rbx]
	mov QWORD PTR [rbx], rax
	mov rax, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rax+240]
	mov rsi, QWORD PTR [rax+112]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2347:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2347b
	mov edx, 1
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+72]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2348:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2348b
	mov r8, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov rsi, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov ebp, 0
	mov r14, 0
2349:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2349b
	mov r15, rbp
	mov ebp, 0
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2350:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2350b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2351:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2351b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+224]
	mov rcx, QWORD PTR [rax+160]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2352:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2353f
	jmp 2354f
2353:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2354:
	test rdx, rdx
	jne 2352b
	mov r15, QWORD PTR [rdi+192]
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
2355:
	mov rax, QWORD PTR [rbx+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2355b
	mov edx, 6
	mov ecx, 5
	mov r8d, 1
	call {vg_rsa_mont_mul_adx}
	mov rdi, QWORD PTR [rdi+128]
237:
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2356:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2356b
	mov rax, QWORD PTR [rdi+240]
	mov rsi, QWORD PTR [rax+112]
	mov r12, QWORD PTR [rax+48]
	mov rbx, QWORD PTR [rdi+80]
	mov r14, 0
2357:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2357b
	mov rax, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rax+112]
	mov r10, QWORD PTR [rax+48]
	mov rax, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rax+64]
	mov r12, QWORD PTR [rax+48]
	mov r8, QWORD PTR [rdi+80]
	mov r13d, 0
2358:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2359:
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
	jne 2359b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 2358b
	mov rbx, QWORD PTR [rdi+80]
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2360:
	mov rbp, rdx
	and rbp, 7
	je 2361f
	jmp 2362f
2361:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2362:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2360b
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
2363:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2363b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
21:
	ret
	.p2align 6
