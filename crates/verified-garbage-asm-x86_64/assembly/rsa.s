// The functions of `src/rsa.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precompute:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov QWORD PTR [r8+128], rdi
	mov QWORD PTR [r8+136], rdx
	mov QWORD PTR [r8+144], rcx
	mov rdi, r8
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
	mov rax, rcx
	and rax, 7
	cmp rax, 0
	je 22f
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
24:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 25f
	jmp 26f
25:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
26:
	test rdx, rdx
	jne 24b
	jmp 23f
22:
	mov r14, rsi
	add r14, rcx
	mov edx, 0
27:
	sub r14, 8
	mov rax, QWORD PTR [r14]
	bswap rax
	mov QWORD PTR [rbx+rdx*1], rax
	add rdx, 8
	cmp rdx, rcx
	jne 27b
23:
	mov r10, rbx
	mov r12, QWORD PTR [rdi+48]
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
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 28f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 210f
212:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 212b
	jmp 211f
210:
211:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
213:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 213b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
214:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
215:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 215b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
216:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 216b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
217:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 217b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 214b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
218:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 218b
	jmp 29f
28:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
219:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 219b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
220:
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
	jne 220b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
221:
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
222:
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
	jne 222b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
223:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 223b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
224:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 224b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 221b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
225:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 225b
29:
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+128]
	mov r14, 0
226:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov rsi, QWORD PTR [rdi+96]
	mov r14, 0
227:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 227b
	mov eax, 1
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
	add rcx, 7
	shr rcx, 3
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov eax, 0
228:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 228b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
21:
	ret
	.p2align 6

vg_rsa_public_precompute_adx:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov QWORD PTR [r8+128], rdi
	mov QWORD PTR [r8+136], rdx
	mov QWORD PTR [r8+144], rcx
	mov rdi, r8
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
	mov rax, rcx
	and rax, 7
	cmp rax, 0
	je 22f
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
24:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 25f
	jmp 26f
25:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
26:
	test rdx, rdx
	jne 24b
	jmp 23f
22:
	mov r14, rsi
	add r14, rcx
	mov edx, 0
27:
	sub r14, 8
	mov rax, QWORD PTR [r14]
	bswap rax
	mov QWORD PTR [rbx+rdx*1], rax
	add rdx, 8
	cmp rdx, rcx
	jne 27b
23:
	mov r10, rbx
	mov r12, QWORD PTR [rdi+48]
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
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 28f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 210f
212:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 212b
	jmp 211f
210:
211:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
213:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 213b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
214:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
215:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 215b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
216:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 216b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
217:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 217b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 214b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
218:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 218b
	jmp 29f
28:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
219:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 219b
	mov r8, rbx
	mov rbx, QWORD PTR [rdi+80]
	mov rsi, r8
	mov r14, 0
220:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 220b
	mov rbx, QWORD PTR [rdi+96]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rcx, rsi
	xor rcx, -1
	mov rdx, rcx
	mulx r14, rax, rsi
	add r14, rsi
	xor r14, -1
	mov rdx, r14
	mulx r11, rax, rcx
	add r14, r11
	add rcx, r14
	mov rdx, rcx
	mulx r14, rax, rsi
	add r14, rsi
	xor r14, -1
	mov rdx, r14
	mulx r11, rax, rcx
	add r14, r11
	add rcx, r14
	mov rdx, rcx
	mulx r14, rax, rsi
	add r14, rsi
	xor r14, -1
	mov rdx, r14
	mulx r11, rax, rcx
	add r14, r11
	add rcx, r14
	mov rdx, rcx
	mulx r14, rax, rsi
	add r14, rsi
	xor r14, -1
	mov rdx, r14
	mulx r11, rax, rcx
	add r14, r11
	add rcx, r14
	mov rdx, rcx
	mulx r14, rax, rsi
	add r14, rsi
	xor r14, -1
	mov rdx, r14
	mulx r11, rax, rcx
	add r14, r11
	add rcx, r14
	mov rdx, rcx
	mulx r14, rax, rsi
	add r14, rsi
	xor r14, -1
	mov rdx, r14
	mulx r11, rax, rcx
	add r14, r11
	add rcx, r14
221:
	mov rdx, rcx
	mulx r14, rax, rsi
	add r14, rsi
	sbb rax, rax
	add rcx, rax
	test rax, rax
	jne 221b
222:
	mov rdx, rcx
	add rdx, 1
	sbb r11, r11
	mulx r14, rax, rsi
	add r14, rsi
	sbb rax, rax
	or rax, r11
	xor rax, -1
	sub rcx, rax
	test rax, rax
	jne 222b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
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
	jb 224f
	jmp 225f
224:
	sub rcx, 1
	add r13, QWORD PTR [r10+r12*8-16]
	adc r14, QWORD PTR [r10+r12*8-8]
	adc r15, 0
225:
	mov r11, r15
	add r11, r11
	jb 226f
	jmp 227f
226:
	sub rcx, 1
	add r13, QWORD PTR [r10+r12*8-16]
	adc r14, QWORD PTR [r10+r12*8-8]
	adc r15, 0
227:
	mov rdx, rcx
	mov rsi, QWORD PTR [rdi+80]
	mov r8d, 0
	mov r9d, 0
	mov r14d, 0
	mov r15d, 0
	mov rax, r12
	and rax, 31
	je 228f
	mov rax, r12
	and rax, 15
	je 230f
232:
	xor rcx, rcx
	add r14, r14
	mulx rax, r11, QWORD PTR [rsi+r15*8]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+8]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+8]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+8], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+16]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+16]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+16], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+24]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+24]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+24], r13
	adox r9, rcx
	sbb r14, r14
	add r15, 4
	cmp r15, r12
	jne 232b
	jmp 231f
230:
233:
	xor rcx, rcx
	add r14, r14
	mulx rax, r11, QWORD PTR [rsi+r15*8]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+8]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+8]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+8], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+16]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+16]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+16], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+24]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+24]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+24], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+32]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+32]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+32], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+40]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+40]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+40], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+48]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+48]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+48], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+56]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+56]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+56], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+64]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+64]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+64], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+72]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+72]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+72], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+80]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+80]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+80], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+88]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+88]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+88], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+96]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+96]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+96], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+104]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+104]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+104], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+112]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+112]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+112], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+120]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+120]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+120], r13
	adox r9, rcx
	sbb r14, r14
	add r15, 16
	cmp r15, r12
	jne 233b
231:
	jmp 229f
228:
234:
	xor rcx, rcx
	add r14, r14
	mulx rax, r11, QWORD PTR [rsi+r15*8]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+8]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+8]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+8], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+16]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+16]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+16], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+24]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+24]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+24], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+32]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+32]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+32], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+40]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+40]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+40], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+48]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+48]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+48], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+56]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+56]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+56], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+64]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+64]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+64], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+72]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+72]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+72], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+80]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+80]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+80], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+88]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+88]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+88], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+96]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+96]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+96], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+104]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+104]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+104], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+112]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+112]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+112], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+120]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+120]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+120], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+128]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+128]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+128], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+136]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+136]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+136], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+144]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+144]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+144], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+152]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+152]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+152], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+160]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+160]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+160], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+168]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+168]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+168], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+176]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+176]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+176], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+184]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+184]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+184], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+192]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+192]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+192], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+200]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+200]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+200], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+208]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+208]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+208], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+216]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+216]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+216], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+224]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+224]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+224], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+232]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+232]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+232], r13
	mulx rax, r11, QWORD PTR [rsi+r15*8+240]
	adox r11, r9
	mov r13, QWORD PTR [rbx+r15*8+240]
	adcx r8, r11
	mov QWORD PTR [rbx+r15*8+240], r8
	mulx r9, r11, QWORD PTR [rsi+r15*8+248]
	adox r11, rax
	mov r8, QWORD PTR [rbx+r15*8+248]
	adcx r13, r11
	mov QWORD PTR [rbx+r15*8+248], r13
	adox r9, rcx
	sbb r14, r14
	add r15, 32
	cmp r15, r12
	jne 234b
229:
	xor rcx, rcx
	add r14, r14
	adcx r8, r9
	sub r8, rdx
	mov QWORD PTR [rbx+r12*8], r8
	mov rax, QWORD PTR [rbx+r12*8]
	add rax, rax
	jb 235f
	jmp 236f
235:
	mov r8, rbx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
237:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 237b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
236:
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 223b
29:
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+128]
	mov r14, 0
238:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 238b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov rsi, QWORD PTR [rdi+96]
	mov r14, 0
239:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 239b
	mov eax, 1
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
	add rcx, 7
	shr rcx, 3
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov eax, 0
240:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 240b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
21:
	ret
	.p2align 6

vg_rsa_private_precompute:
	mov r11, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov QWORD PTR [r11+128], rdi
	mov QWORD PTR [r11+136], rdx
	mov QWORD PTR [r11+144], rcx
	mov QWORD PTR [r11+168], rdi
	mov QWORD PTR [r11+152], r8
	mov QWORD PTR [r11+160], r9
	mov QWORD PTR [r11+200], r8
	mov QWORD PTR [r11+224], rdi
	mov QWORD PTR [r11+184], r10
	mov QWORD PTR [r11+216], r10
	mov QWORD PTR [r11+192], rax
	mov rdi, r11
	mov rcx, rsi
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov rsi, QWORD PTR [rdi+128]
	mov eax, 0
20:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 20b
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
	jne 21f
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
23:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 24f
	jmp 25f
24:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
25:
	test rdx, rdx
	jne 23b
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+144]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
26:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 27f
	jmp 28f
27:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
28:
	test rdx, rdx
	jne 26b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
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
210:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 210b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 211f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 213f
215:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 215b
	jmp 214f
213:
214:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
216:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 216b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
217:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
218:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 218b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
219:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 219b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
220:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 220b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 217b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
221:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 221b
	jmp 212f
211:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
222:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
223:
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
	jne 223b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
224:
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
225:
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
	jne 225b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
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
	jne 224b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
228:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 228b
212:
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul}
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
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
255:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 255b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+96]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
256:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
257:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 257b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 258f
	mov r12, QWORD PTR [rdi+48]
	jmp 259f
258:
259:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
260:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
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
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
261:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 261b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
262:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 262b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
263:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 256b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
264:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	mov rax, QWORD PTR [rdi+48]
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	mov ecx, 0
265:
	add rcx, rax
	cmp rcx, r12
	jb 265b
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rcx, rax
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	mov QWORD PTR [rdi+248], rcx
	cmp rcx, r12
	jb 266f
	jmp 267f
266:
268:
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rcx
	cmp rcx, r12
	jb 268b
267:
	mov rcx, QWORD PTR [rdi+248]
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	sub rcx, r12
	je 269f
	mov QWORD PTR [rdi+176], rcx
271:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
272:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 272b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
273:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 273b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
274:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 274b
	mov rcx, QWORD PTR [rdi+176]
	sub rcx, 1
	mov QWORD PTR [rdi+176], rcx
	jne 271b
	jmp 270f
269:
270:
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
275:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 275b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+96]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
276:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
277:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 278f
	mov r12, QWORD PTR [rdi+48]
	jmp 279f
278:
279:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
280:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 280b
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
	call {vg_rsa_mont_mul}
	mov edx, 5
	mov ecx, 1
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov rbx, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
281:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 281b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
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
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 276b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
284:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 284b
	mov rax, QWORD PTR [rdi+48]
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	mov ecx, 0
285:
	add rcx, rax
	cmp rcx, r12
	jb 285b
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rcx, rax
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	mov QWORD PTR [rdi+248], rcx
	cmp rcx, r12
	jb 286f
	jmp 287f
286:
288:
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul}
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rcx
	cmp rcx, r12
	jb 288b
287:
	mov rcx, QWORD PTR [rdi+248]
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	sub rcx, r12
	je 289f
	mov QWORD PTR [rdi+176], rcx
291:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
292:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 292b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
293:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 293b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
294:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 294b
	mov rcx, QWORD PTR [rdi+176]
	sub rcx, 1
	mov QWORD PTR [rdi+176], rcx
	jne 291b
	jmp 290f
289:
290:
	mov rdi, QWORD PTR [rdi+128]
	mov rbx, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+176]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov r14, 0
295:
	mov rax, QWORD PTR [rsi+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 295b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov r14, 0
296:
	mov rax, QWORD PTR [rsi+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov rdi, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov r14, 0
297:
	mov rax, QWORD PTR [rsi+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov r14, 0
298:
	mov rax, QWORD PTR [rsi+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 298b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+176]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 22f
21:
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov eax, 0
299:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 299b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
22:
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_rsa_private_precompute_adx:
	mov r11, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov QWORD PTR [r11+128], rdi
	mov QWORD PTR [r11+136], rdx
	mov QWORD PTR [r11+144], rcx
	mov QWORD PTR [r11+168], rdi
	mov QWORD PTR [r11+152], r8
	mov QWORD PTR [r11+160], r9
	mov QWORD PTR [r11+200], r8
	mov QWORD PTR [r11+224], rdi
	mov QWORD PTR [r11+184], r10
	mov QWORD PTR [r11+216], r10
	mov QWORD PTR [r11+192], rax
	mov rdi, r11
	mov rcx, rsi
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov rsi, QWORD PTR [rdi+128]
	mov eax, 0
20:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 20b
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
	jne 21f
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
23:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 24f
	jmp 25f
24:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
25:
	test rdx, rdx
	jne 23b
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+144]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
26:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 27f
	jmp 28f
27:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
28:
	test rdx, rdx
	jne 26b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
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
210:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 210b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 211f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 213f
215:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 215b
	jmp 214f
213:
214:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
216:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 216b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
217:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
218:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 218b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
219:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 219b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
220:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 220b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 217b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
221:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 221b
	jmp 212f
211:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
222:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
223:
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
	jne 223b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
224:
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
225:
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
	jne 225b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
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
	jne 224b
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
212:
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
	mov rdi, QWORD PTR [rdi+232]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
255:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 255b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+96]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
256:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
257:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 257b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 258f
	mov r12, QWORD PTR [rdi+48]
	jmp 259f
258:
259:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
260:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
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
261:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 261b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
262:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 262b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
263:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 256b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
264:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	mov rax, QWORD PTR [rdi+48]
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	mov ecx, 0
265:
	add rcx, rax
	cmp rcx, r12
	jb 265b
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rcx, rax
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	mov QWORD PTR [rdi+248], rcx
	cmp rcx, r12
	jb 266f
	jmp 267f
266:
268:
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rcx
	cmp rcx, r12
	jb 268b
267:
	mov rcx, QWORD PTR [rdi+248]
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	sub rcx, r12
	je 269f
	mov QWORD PTR [rdi+176], rcx
271:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
272:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 272b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
273:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 273b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
274:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 274b
	mov rcx, QWORD PTR [rdi+176]
	sub rcx, 1
	mov QWORD PTR [rdi+176], rcx
	jne 271b
	jmp 270f
269:
270:
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
275:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 275b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+96]
	mov QWORD PTR [rdi+184], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rdi+176], rdx
276:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
277:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+176]
	cmp r12, QWORD PTR [rdi+48]
	jb 278f
	mov r12, QWORD PTR [rdi+48]
	jmp 279f
278:
279:
	mov rsi, QWORD PTR [rdi+184]
	mov rbx, QWORD PTR [rdi+72]
	mov r14, 0
280:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 280b
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
281:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 281b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+96]
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
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	jne 276b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
284:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 284b
	mov rax, QWORD PTR [rdi+48]
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	mov ecx, 0
285:
	add rcx, rax
	cmp rcx, r12
	jb 285b
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rcx, rax
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	mov QWORD PTR [rdi+248], rcx
	cmp rcx, r12
	jb 286f
	jmp 287f
286:
288:
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rcx
	cmp rcx, r12
	jb 288b
287:
	mov rcx, QWORD PTR [rdi+248]
	mov r12, QWORD PTR [rdi+128]
	mov r12, QWORD PTR [r12+48]
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	add r12, r12
	sub rcx, r12
	je 289f
	mov QWORD PTR [rdi+176], rcx
291:
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
292:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 292b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
293:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 293b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
294:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 294b
	mov rcx, QWORD PTR [rdi+176]
	sub rcx, 1
	mov QWORD PTR [rdi+176], rcx
	jne 291b
	jmp 290f
289:
290:
	mov rdi, QWORD PTR [rdi+128]
	mov rbx, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+176]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov r14, 0
295:
	mov rax, QWORD PTR [rsi+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 295b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov r14, 0
296:
	mov rax, QWORD PTR [rsi+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov rdi, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov r14, 0
297:
	mov rax, QWORD PTR [rsi+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov r14, 0
298:
	mov rax, QWORD PTR [rsi+r14*8]
	and rax, r15
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 298b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+176]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 22f
21:
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov eax, 0
299:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 299b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
22:
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_rsa_crt_values:
	mov r11, QWORD PTR [rsp+72]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov QWORD PTR [r11+128], rdi
	mov QWORD PTR [r11+168], rsi
	mov QWORD PTR [r11+152], rdx
	mov QWORD PTR [r11+184], rcx
	mov QWORD PTR [r11+160], r8
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [r11+216], rax
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
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+224], rax
	mov rax, -1
	mov QWORD PTR [rdi+176], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
22:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 22b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
23:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 24f
	jmp 25f
24:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
25:
	test rdx, rdx
	jne 23b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
26:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 26b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+192]
	mov rcx, QWORD PTR [rdi+168]
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
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
210:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 210b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
211:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 212f
	jmp 213f
212:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
213:
	test rdx, rdx
	jne 211b
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
214:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 214b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+208]
	mov rcx, QWORD PTR [rdi+216]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
215:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 216f
	jmp 217f
216:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
217:
	test rdx, rdx
	jne 215b
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 218b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r11, r9
	add r11, rdi
	add r11, 256
	mov rax, r9
	add rax, rax
	add rax, rax
	add rax, rdi
	add rax, 256
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r9, rax
	mov r10, QWORD PTR [rdi+168]
	add r10, 7
	shr r10, 3
	mov r12, QWORD PTR [rdi+184]
	add r12, 7
	shr r12, 3
	mov r13d, 0
219:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
220:
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
	jne 220b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 219b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+80]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
221:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 221b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	add r12, 2
	mov r14, 0
222:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 222b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rdx, QWORD PTR [rdi+136]
	mov rax, r12
	and rax, 1
	mov rcx, r12
	shl rcx, 3
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+168]
	shl rcx, 1
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+168]
	xor rcx, QWORD PTR [rdi+184]
	or rax, rcx
	movzx ecx, BYTE PTR [rdx]
	shr rcx, 7
	xor rcx, 1
	or rax, rcx
	je 223f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+184]
	cmp r13, rax
	cmovb r13, rax
	add r13, 7
	shr r13, 3
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
225:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 225b
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
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
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
227:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 227b
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
228:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 228b
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
229:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 229b
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
230:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 230b
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
231:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 231b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	mov rsi, r9
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
232:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
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
233:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 233b
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
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
234:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 234b
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
235:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 235b
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
236:
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
	mov QWORD PTR [rdi+32], rcx
	mov rcx, QWORD PTR [rdi+40]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov QWORD PTR [rdi+40], rcx
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov QWORD PTR [rdi+48], rcx
	mov rcx, QWORD PTR [rdi+56]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+8], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov QWORD PTR [rdi+56], rcx
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r15, 1
	shl r15, 3
	add r15, r8
	mov rcx, QWORD PTR [rdi+32]
	mov r14, QWORD PTR [rdi+40]
	mov r10, QWORD PTR [rdi+32]
	and r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [rdi+40]
	and rax, QWORD PTR [rdi+72]
	add r10, rax
	mov r11d, 0
	mov r12, QWORD PTR [rdi+48]
	and r12, QWORD PTR [rdi]
	mov rax, QWORD PTR [rdi+56]
	and rax, QWORD PTR [rdi+8]
	add r12, rax
	mov r13d, 0
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul r14
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rbx, r10
	mov r10, r11
	mov r11d, 0
	mov rbp, r12
	mov r12, r13
	mov r13d, 0
	add r8, 8
237:
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul r14
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rax, rbx
	shr rax, 59
	mov rbx, r10
	shl r10, 5
	add rax, r10
	mov QWORD PTR [r8-8], rax
	mov r10, r11
	mov r11d, 0
	mov rax, rbp
	shr rax, 59
	mov rbp, r12
	shl r12, 5
	add rax, r12
	mov QWORD PTR [r8+r9*1-8], rax
	mov r12, r13
	mov r13d, 0
	add r8, 8
	cmp r8, r15
	jne 237b
	mov rax, rbx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	shl rdx, 5
	mov rax, rbx
	shr rax, 59
	add rax, rdx
	mov QWORD PTR [r8-8], rax
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	shl rdx, 5
	mov rax, rbp
	shr rax, 59
	add rax, rdx
	mov QWORD PTR [r8+r9*1-8], rax
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	sub r15, rax
	shr r15, 3
	sub r15, 1
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r15, 1
	shl r15, 3
	add r15, r8
	mov rcx, QWORD PTR [rdi+32]
	mov rbp, QWORD PTR [rdi+40]
	mov r10, QWORD PTR [rdi+32]
	and r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [rdi+40]
	and rax, QWORD PTR [rdi+72]
	add r10, rax
	mov r11d, 0
	mov r12d, 0
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, r10
	mov rdx, QWORD PTR [rdi+80]
	mul rdx
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [r8+r9*4]
	mov rdx, QWORD PTR [rdi+16]
	mul rdx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov r10, r11
	mov r11, r12
	mov r12d, 0
	mov r13, QWORD PTR [rdi+48]
	and r13, QWORD PTR [rdi]
	mov rax, QWORD PTR [rdi+56]
	and rax, QWORD PTR [rdi+8]
	add r13, rax
	mov r14d, 0
	mov ebx, 0
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, r13
	mov rdx, QWORD PTR [rdi+80]
	mul rdx
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [r8+r9*4]
	mov rdx, QWORD PTR [rdi+88]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov r13, r14
	mov r14, rbx
	mov ebx, 0
	add r8, 8
238:
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8+r9*4]
	mov rdx, QWORD PTR [rdi+16]
	mul rdx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, QWORD PTR [r8+r9*4]
	mov rdx, QWORD PTR [rdi+88]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov QWORD PTR [r8-8], r10
	mov QWORD PTR [r8+r9*1-8], r13
	mov r10, r11
	mov r11, r12
	mov r12d, 0
	mov r13, r14
	mov r14, rbx
	mov ebx, 0
	add r8, 8
	cmp r8, r15
	jne 238b
	mov rax, QWORD PTR [r8-8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	xor rax, QWORD PTR [rdi+64]
	mov rcx, QWORD PTR [rdi+32]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8-8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	xor rax, QWORD PTR [rdi]
	mov rcx, QWORD PTR [rdi+48]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, QWORD PTR [r8+r9*1-8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	xor rax, QWORD PTR [rdi+72]
	mov rcx, QWORD PTR [rdi+40]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8+r9*1-8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	xor rax, QWORD PTR [rdi+8]
	mov rcx, QWORD PTR [rdi+56]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov QWORD PTR [r8-8], r10
	mov QWORD PTR [r8+r9*1-8], r13
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	add rax, r9
	add rax, r9
	sub r15, rax
	shr r15, 3
	sub r15, 1
	sub rsi, 1
	jne 236b
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
239:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 239b
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
240:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 240b
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
241:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 241b
	mov r14, 0
242:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
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
243:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 243b
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
244:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 244b
	mov r11, r13
	shl r11, 4
	sub r11, r13
	add r11, 10
245:
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
246:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 246b
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
247:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 247b
	mov r14, 0
248:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 248b
	sub r11, 1
	jne 245b
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
249:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 249b
	mov r14, 0
250:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
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
251:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
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
252:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 252b
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
253:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 253b
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
254:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
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
255:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 255b
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
256:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 256b
	jmp 224f
223:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+184]
	cmp r13, rax
	cmovb r13, rax
	add r13, 7
	shr r13, 3
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
257:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 257b
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
258:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
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
259:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 259b
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
260:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
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
261:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
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
262:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 262b
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
263:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
	mov rsi, r9
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
264:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
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
265:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 265b
	mov r12, r13
	mov rsi, r9
	add rsi, rsi
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
266:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 266b
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
267:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 267b
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
268:
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
	mov QWORD PTR [rdi+32], rcx
	mov rcx, QWORD PTR [rdi+40]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov QWORD PTR [rdi+40], rcx
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov QWORD PTR [rdi+48], rcx
	mov rcx, QWORD PTR [rdi+56]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+8], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov QWORD PTR [rdi+56], rcx
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r15, 1
	shl r15, 3
	add r15, r8
	mov rcx, QWORD PTR [rdi+32]
	mov r14, QWORD PTR [rdi+40]
	mov r10, QWORD PTR [rdi+32]
	and r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [rdi+40]
	and rax, QWORD PTR [rdi+72]
	add r10, rax
	mov r11d, 0
	mov r12, QWORD PTR [rdi+48]
	and r12, QWORD PTR [rdi]
	mov rax, QWORD PTR [rdi+56]
	and rax, QWORD PTR [rdi+8]
	add r12, rax
	mov r13d, 0
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul r14
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rbx, r10
	mov r10, r11
	mov r11d, 0
	mov rbp, r12
	mov r12, r13
	mov r13d, 0
	add r8, 8
269:
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul r14
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rax, rbx
	shr rax, 59
	mov rbx, r10
	shl r10, 5
	add rax, r10
	mov QWORD PTR [r8-8], rax
	mov r10, r11
	mov r11d, 0
	mov rax, rbp
	shr rax, 59
	mov rbp, r12
	shl r12, 5
	add rax, r12
	mov QWORD PTR [r8+r9*1-8], rax
	mov r12, r13
	mov r13d, 0
	add r8, 8
	cmp r8, r15
	jne 269b
	mov rax, rbx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	shl rdx, 5
	mov rax, rbx
	shr rax, 59
	add rax, rdx
	mov QWORD PTR [r8-8], rax
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	shl rdx, 5
	mov rax, rbp
	shr rax, 59
	add rax, rdx
	mov QWORD PTR [r8+r9*1-8], rax
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	sub r15, rax
	shr r15, 3
	sub r15, 1
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r8, r9
	add r15, 1
	shl r15, 3
	add r15, r8
	mov rcx, QWORD PTR [rdi+32]
	mov rbp, QWORD PTR [rdi+40]
	mov r10, QWORD PTR [rdi+32]
	and r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [rdi+40]
	and rax, QWORD PTR [rdi+72]
	add r10, rax
	mov r11d, 0
	mov r12d, 0
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, r10
	mov rdx, QWORD PTR [rdi+80]
	mul rdx
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [r8+r9*4]
	mov rdx, QWORD PTR [rdi+16]
	mul rdx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov r10, r11
	mov r11, r12
	mov r12d, 0
	mov r13, QWORD PTR [rdi+48]
	and r13, QWORD PTR [rdi]
	mov rax, QWORD PTR [rdi+56]
	and rax, QWORD PTR [rdi+8]
	add r13, rax
	mov r14d, 0
	mov ebx, 0
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, r13
	mov rdx, QWORD PTR [rdi+80]
	mul rdx
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [r8+r9*4]
	mov rdx, QWORD PTR [rdi+88]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov r13, r14
	mov r14, rbx
	mov ebx, 0
	add r8, 8
270:
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul rbp
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8+r9*4]
	mov rdx, QWORD PTR [rdi+16]
	mul rdx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, QWORD PTR [r8+r9*4]
	mov rdx, QWORD PTR [rdi+88]
	mul rdx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov QWORD PTR [r8-8], r10
	mov QWORD PTR [r8+r9*1-8], r13
	mov r10, r11
	mov r11, r12
	mov r12d, 0
	mov r13, r14
	mov r14, rbx
	mov ebx, 0
	add r8, 8
	cmp r8, r15
	jne 270b
	mov rax, QWORD PTR [r8-8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	xor rax, QWORD PTR [rdi+64]
	mov rcx, QWORD PTR [rdi+32]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8-8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	xor rax, QWORD PTR [rdi]
	mov rcx, QWORD PTR [rdi+48]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov rax, QWORD PTR [r8+r9*1-8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	xor rax, QWORD PTR [rdi+72]
	mov rcx, QWORD PTR [rdi+40]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [r8+r9*1-8]
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	xor rax, QWORD PTR [rdi+8]
	mov rcx, QWORD PTR [rdi+56]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc rbx, 0
	mov QWORD PTR [r8-8], r10
	mov QWORD PTR [r8+r9*1-8], r13
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	add rax, r9
	add rax, r9
	sub r15, rax
	shr r15, 3
	sub r15, 1
	sub rsi, 1
	jne 268b
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
271:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
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
272:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 272b
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
273:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 273b
	mov r14, 0
274:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 274b
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
275:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 275b
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
276:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 276b
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
277:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 277b
	mov r14, 0
278:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 278b
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
279:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
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
280:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 280b
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
281:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
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
283:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
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
284:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 284b
224:
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
285:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 285b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
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
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
286:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 286b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rdx, QWORD PTR [rdi+136]
	mov rax, r12
	and rax, 1
	mov rcx, r12
	shl rcx, 3
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+168]
	shl rcx, 1
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+168]
	xor rcx, QWORD PTR [rdi+184]
	or rax, rcx
	movzx ecx, BYTE PTR [rdx]
	shr rcx, 7
	xor rcx, 1
	or rax, rcx
	je 287f
	jmp 288f
287:
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
289:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 289b
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
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
290:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 290b
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
291:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 291b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	mov rax, r12
	shl rax, 4
	sub rax, r12
	add rax, 10
	mov rcx, rax
	and rcx, 63
	shr rax, 6
	shl rax, 3
	add r12, 1
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, rax
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
292:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 292b
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
293:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 293b
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
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
294:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 294b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	shr r12, 1
	mov rax, QWORD PTR [r10+r12*8-8]
	movabs rdx, -9223372036854775808
	or rax, rdx
	mov QWORD PTR [r10+r12*8-8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
295:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 295b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	mov rax, r12
	shl rax, 4
	sub rax, r12
	add rax, 10
	shr rax, 6
	add rax, 2
	shl rax, 3
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, rax
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	sub r12, 1
	mov r14, 0
296:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
297:
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
	jne 297b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	shr r12, 1
	mov rax, r12
	shl rax, 4
	sub rax, r12
	add rax, 10
	shr rax, 6
	add rax, 2
	mov QWORD PTR [rbp+16], rax
298:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rbp+16]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
299:
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
	jne 299b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2100:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2101:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2101b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, QWORD PTR [rbp+16]
	sub rax, 1
	mov QWORD PTR [rbp+16], rax
	jne 298b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2102:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2102b
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
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2103:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
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
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2104:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
288:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rdx, QWORD PTR [rdi+136]
	mov rax, r12
	and rax, 1
	mov rcx, r12
	shl rcx, 3
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+168]
	shl rcx, 1
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+168]
	xor rcx, QWORD PTR [rdi+184]
	or rax, rcx
	movzx ecx, BYTE PTR [rdx]
	shr rcx, 7
	xor rcx, 1
	or rax, rcx
	je 2105f
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
2107:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
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
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2108:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2108b
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
	sub rax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2109:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2109b
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
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2110:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2110b
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
2111:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
2112:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2113:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
2114:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2114b
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
2115:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2115b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
2116:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2116b
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
	jne 2112b
	jmp 2106f
2105:
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
2117:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2117b
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
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2118:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2118b
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
	sub rax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2119:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
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
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2120:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	shr r12, 1
	mov rax, QWORD PTR [r10+r12*8-8]
	movabs rdx, -9223372036854775808
	or rax, rdx
	mov QWORD PTR [r10+r12*8-8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	shl rax, 3
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, rax
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	sub r12, 1
	mov r14, 0
2122:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2123:
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
	jne 2123b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	mov QWORD PTR [rbp+16], rax
2124:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rbp+16]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2125:
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
	jne 2125b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2126:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2127:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2127b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, QWORD PTR [rbp+16]
	sub rax, 1
	mov QWORD PTR [rbp+16], rax
	jne 2124b
2106:
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
2128:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2128b
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
2129:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rdx, QWORD PTR [rdi+136]
	mov rax, r12
	and rax, 1
	mov rcx, r12
	shl rcx, 3
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+168]
	shl rcx, 1
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+168]
	xor rcx, QWORD PTR [rdi+184]
	or rax, rcx
	movzx ecx, BYTE PTR [rdx]
	shr rcx, 7
	xor rcx, 1
	or rax, rcx
	je 2130f
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
2132:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2132b
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
2133:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2133b
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
	sub rax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2134:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2134b
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
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2135:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2135b
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
2136:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2136b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
2137:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2138:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
2139:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2139b
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
2140:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2140b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
2141:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2141b
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
	jne 2137b
	jmp 2131f
2130:
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
2142:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2142b
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
2143:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2143b
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
	sub rax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2144:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
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
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2145:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2145b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	shr r12, 1
	mov rax, QWORD PTR [r10+r12*8-8]
	movabs rdx, -9223372036854775808
	or rax, rdx
	mov QWORD PTR [r10+r12*8-8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2146:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	shl rax, 3
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, rax
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	sub r12, 1
	mov r14, 0
2147:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2147b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2148:
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
	jne 2148b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	mov QWORD PTR [rbp+16], rax
2149:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rbp+16]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2150:
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
	jne 2150b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2151:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2151b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2152:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, QWORD PTR [rbp+16]
	sub rax, 1
	mov QWORD PTR [rbp+16], rax
	jne 2149b
2131:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+160]
	mov rcx, QWORD PTR [rdi+168]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2153:
	mov rbp, rdx
	and rbp, 7
	je 2154f
	jmp 2155f
2154:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2155:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2153b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+168]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2156:
	mov rbp, rdx
	and rbp, 7
	je 2157f
	jmp 2158f
2157:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2158:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2156b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+152]
	mov rcx, QWORD PTR [rdi+184]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2159:
	mov rbp, rdx
	and rbp, 7
	je 2160f
	jmp 2161f
2160:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2161:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2159b
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
	mov rcx, QWORD PTR [rdi+168]
	mov eax, 0
2162:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2162b
	mov rsi, QWORD PTR [rdi+152]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
2163:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2163b
	mov rsi, QWORD PTR [rdi+160]
	mov rcx, QWORD PTR [rdi+168]
	mov eax, 0
2164:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2164b
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
21:
	ret
	.p2align 6

vg_rsa_recover_primes_det:
	mov r11, QWORD PTR [rsp+40]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov QWORD PTR [r11+128], rdi
	mov QWORD PTR [r11+168], rdx
	mov QWORD PTR [r11+136], r8
	mov QWORD PTR [r11+144], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11+160], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r11+192], rax
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
	mov r12, QWORD PTR [rdi+144]
	add r12, 7
	shr r12, 3
	add r12, 1
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
	mov rax, -1
	mov QWORD PTR [rdi+176], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
22:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 22b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
23:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 24f
	jmp 25f
24:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
25:
	test rdx, rdx
	jne 23b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
26:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 26b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
27:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 27b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+152]
	mov rcx, QWORD PTR [rdi+160]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
28:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 29f
	jmp 210f
29:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
210:
	test rdx, rdx
	jne 28b
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
211:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 211b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+184]
	mov rcx, QWORD PTR [rdi+192]
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
215:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 215b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
216:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 216b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r15, r9
	add r15, r15
	add r15, r15
	add r15, r15
	add r15, r9
	add r15, rdi
	add r15, 256
	mov r11, QWORD PTR [rdi+160]
	add r11, 7
	shr r11, 3
	mov r13d, 0
217:
	mov rcx, QWORD PTR [rbx+r13*8]
	mov r8, r13
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r10
	mov r9, r15
	mov ebp, 0
	mov r14, 0
218:
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
	jne 218b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r11
	jne 217b
	mov r12, QWORD PTR [rdi+144]
	add r12, 7
	shr r12, 3
	add r12, 1
	add r12, r12
	add r12, 2
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
	mov r8, r9
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
	add rbx, rdi
	add rbx, 256
	mov eax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
220:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 220b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
221:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 221b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r12, QWORD PTR [rdi+144]
	add r12, 7
	shr r12, 3
	add r12, 1
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
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
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
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
223:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 223b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
224:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 224b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
225:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 225b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
227:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 227b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 66
	jb 228f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 64
	mov r14, 0
230:
	mov rax, QWORD PTR [rbx+r14*8]
	or rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 230b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
231:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 231b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 64
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 512
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
232:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
233:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 233b
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
234:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 234b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 64
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 512
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
235:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 235b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
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
237:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 237b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
238:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 238b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	sub r12, 64
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add rbx, 512
	mov r14, 0
239:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 239b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
240:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 240b
	jmp 229f
228:
229:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 34
	jb 241f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 32
	mov r14, 0
243:
	mov rax, QWORD PTR [rbx+r14*8]
	or rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 243b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
244:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 244b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 32
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
245:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 245b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
246:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 246b
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
247:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 247b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 32
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
248:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 248b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
249:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 249b
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
250:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
251:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	sub r12, 32
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add rbx, 256
	mov r14, 0
252:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 252b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
253:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 253b
	jmp 242f
241:
242:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 18
	jb 254f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 16
	mov r14, 0
256:
	mov rax, QWORD PTR [rbx+r14*8]
	or rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 256b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
257:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 257b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 16
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 128
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
258:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
259:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 259b
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
260:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 16
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 128
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
261:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
262:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 262b
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
263:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
264:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	sub r12, 16
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add rbx, 128
	mov r14, 0
265:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 265b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
266:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 266b
	jmp 255f
254:
255:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 10
	jb 267f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 8
	mov r14, 0
269:
	mov rax, QWORD PTR [rbx+r14*8]
	or rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 269b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
270:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 270b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 8
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 64
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
271:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
272:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
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
273:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 8
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 64
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
274:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 274b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
275:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 275b
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
276:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 276b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
277:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	sub r12, 8
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add rbx, 64
	mov r14, 0
278:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 278b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
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
	jmp 268f
267:
268:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 6
	jb 280f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 4
	mov r14, 0
282:
	mov rax, QWORD PTR [rbx+r14*8]
	or rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 282b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
283:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 4
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 32
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
284:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 284b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
285:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
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
	sub r12, 4
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 32
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
287:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 287b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
288:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 288b
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
289:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 289b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
290:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 290b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	sub r12, 4
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add rbx, 32
	mov r14, 0
291:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 291b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
292:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 292b
	jmp 281f
280:
281:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 4
	jb 293f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 2
	mov r14, 0
295:
	mov rax, QWORD PTR [rbx+r14*8]
	or rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 295b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 16
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
297:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
298:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 298b
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
299:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 299b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 16
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2100:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2101:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2101b
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
2102:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2103:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add rbx, 16
	mov r14, 0
2104:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2105:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2105b
	jmp 294f
293:
294:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 3
	jb 2106f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 1
	mov r14, 0
2108:
	mov rax, QWORD PTR [rbx+r14*8]
	or rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2108b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2109:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 1
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 8
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2110:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2110b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2111:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2111b
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
2112:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 1
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 8
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2113:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2114:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
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
2115:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2115b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2116:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2116b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	sub r12, 1
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add rbx, 8
	mov r14, 0
2117:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2117b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2118:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2118b
	jmp 2107f
2106:
2107:
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	or rax, QWORD PTR [r10]
	shl rax, 32
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 32
	mov r14, 0
2119:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
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
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov ecx, 32
	mov r14, 0
2121:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2122:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov ecx, 32
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2123:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2124:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2124b
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	or rax, QWORD PTR [r10]
	shl rax, 48
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 16
	mov r14, 0
2125:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2125b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2126:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov ecx, 16
	mov r14, 0
2127:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2127b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2128:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2128b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov ecx, 16
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2129:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2130:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2130b
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	or rax, QWORD PTR [r10]
	shl rax, 56
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 8
	mov r14, 0
2131:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2131b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2132:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2132b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov ecx, 8
	mov r14, 0
2133:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2134:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2134b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov ecx, 8
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2135:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2135b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2136:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2136b
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	or rax, QWORD PTR [r10]
	shl rax, 60
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 4
	mov r14, 0
2137:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2137b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2138:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2138b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov ecx, 4
	mov r14, 0
2139:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2139b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2140:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2140b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov ecx, 4
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2141:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2141b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2142:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2142b
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	or rax, QWORD PTR [r10]
	shl rax, 62
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 2
	mov r14, 0
2143:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2143b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2144:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov ecx, 2
	mov r14, 0
2145:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2145b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2146:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov ecx, 2
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2147:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2147b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	or rax, QWORD PTR [r10]
	shl rax, 63
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 1
	mov r14, 0
2149:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
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
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov ecx, 1
	mov r14, 0
2151:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2151b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2152:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov ecx, 1
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2153:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2153b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov rbp, QWORD PTR [rdi+216]
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
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 66
	jb 2155f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 64
	mov r14, 0
2157:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2158:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2158b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 64
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 512
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2159:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
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
	jmp 2156f
2155:
2156:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 34
	jb 2161f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 32
	mov r14, 0
2163:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2163b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2164:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 32
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2165:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2165b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2166:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2166b
	jmp 2162f
2161:
2162:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 18
	jb 2167f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 16
	mov r14, 0
2169:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2170:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2170b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 16
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 128
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2171:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2172:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2172b
	jmp 2168f
2167:
2168:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 10
	jb 2173f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 8
	mov r14, 0
2175:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2175b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2176:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2176b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 8
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 64
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
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
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2178:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2178b
	jmp 2174f
2173:
2174:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 6
	jb 2179f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 4
	mov r14, 0
2181:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2182:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 4
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 32
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2183:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2184:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2184b
	jmp 2180f
2179:
2180:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 4
	jb 2185f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 2
	mov r14, 0
2187:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2187b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2188:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2188b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 16
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2189:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2189b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2190:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2190b
	jmp 2186f
2185:
2186:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 3
	jb 2191f
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r12d, 1
	mov r14, 0
2193:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2193b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2194:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2194b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 1
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, 8
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2195:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2195b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2196:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2196b
	jmp 2192f
2191:
2192:
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	shl rax, 32
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 32
	mov r14, 0
2197:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2197b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2198:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2198b
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	shl rax, 48
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 16
	mov r14, 0
2199:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2199b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2200:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2200b
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	shl rax, 56
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 8
	mov r14, 0
2201:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2201b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2202:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2202b
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	shl rax, 60
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 4
	mov r14, 0
2203:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2203b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2204:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2204b
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	shl rax, 62
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 2
	mov r14, 0
2205:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2205b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2206:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2206b
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
	add r10, rdi
	add r10, 256
	mov rax, QWORD PTR [rbx]
	shl rax, 63
	mov rbp, rax
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov ecx, 1
	mov r14, 0
2207:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2207b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2208:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2208b
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
2209:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2209b
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
2210:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2210b
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
2211:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2211b
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
2212:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2212b
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
2213:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2213b
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
2214:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2214b
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
2215:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2215b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, r13
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
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2216:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2216b
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
2217:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2217b
	mov r12, r13
	mov rsi, r9
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
2219:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2219b
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
2220:
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
	mov QWORD PTR [rdi+32], rcx
	mov rcx, QWORD PTR [rdi+40]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+72], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov QWORD PTR [rdi+40], rcx
	mov rcx, QWORD PTR [rdi+48]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov QWORD PTR [rdi+48], rcx
	mov rcx, QWORD PTR [rdi+56]
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+8], rdx
	xor rcx, rdx
	sub rcx, rdx
	mov QWORD PTR [rdi+56], rcx
	mov r8, rdi
	add r8, r9
	add r8, r9
	add r8, r9
	add r15, 1
	shl r15, 3
	add r15, r8
	mov rcx, QWORD PTR [rdi+32]
	mov r14, QWORD PTR [rdi+40]
	mov r10, QWORD PTR [rdi+32]
	and r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [rdi+40]
	and rax, QWORD PTR [rdi+72]
	add r10, rax
	mov r11d, 0
	mov r12, QWORD PTR [rdi+48]
	and r12, QWORD PTR [rdi]
	mov rax, QWORD PTR [rdi+56]
	and rax, QWORD PTR [rdi+8]
	add r12, rax
	mov r13d, 0
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul r14
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rbx, r10
	mov r10, r11
	mov r11d, 0
	mov rbp, r12
	mov r12, r13
	mov r13d, 0
	add r8, 8
2221:
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+72]
	mul r14
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rdi]
	mov rdx, QWORD PTR [rdi+48]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rax, QWORD PTR [r8+r9*1]
	xor rax, QWORD PTR [rdi+8]
	mov rdx, QWORD PTR [rdi+56]
	mul rdx
	add r12, rax
	adc r13, rdx
	mov rax, rbx
	shr rax, 59
	mov rbx, r10
	shl r10, 5
	add rax, r10
	mov QWORD PTR [r8-8], rax
	mov r10, r11
	mov r11d, 0
	mov rax, rbp
	shr rax, 59
	mov rbp, r12
	shl r12, 5
	add rax, r12
	mov QWORD PTR [r8+r9*1-8], rax
	mov r12, r13
	mov r13d, 0
	add r8, 8
	cmp r8, r15
	jne 2221b
	mov rax, rbx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	shl rdx, 5
	mov rax, rbx
	shr rax, 59
	add rax, rdx
	mov QWORD PTR [r8-8], rax
	mov rax, rbp
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	shl rdx, 5
	mov rax, rbp
	shr rax, 59
	add rax, rdx
	mov QWORD PTR [r8+r9*1-8], rax
	mov rax, rdi
	add rax, r9
	add rax, r9
	add rax, r9
	sub r15, rax
	shr r15, 3
	sub r15, 1
	sub rsi, 1
	jne 2220b
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
	add r8, r8
	add r8, r9
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
2223:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2223b
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
2224:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2224b
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
2225:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2225b
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
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2226:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2226b
	mov r12, QWORD PTR [rdi+144]
	add r12, 7
	shr r12, 3
	add r12, 1
	add r12, r12
	add r12, 2
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
	mov rax, r12
	add rax, rax
	add rax, rax
	sub rax, 8
	mov QWORD PTR [rdi+160], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2227:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2227b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
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
2228:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2228b
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
2229:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2229b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2230:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2230b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r15, r9
	add r15, r15
	add r15, r15
	add r15, r15
	add r15, r9
	add r15, rdi
	add r15, 256
	mov r11, QWORD PTR [rdi+160]
	add r11, 7
	shr r11, 3
	mov r13d, 0
2231:
	mov rcx, QWORD PTR [rbx+r13*8]
	mov r8, r13
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r10
	mov r9, r15
	mov ebp, 0
	mov r14, 0
2232:
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
	jne 2232b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r11
	jne 2231b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov r11d, 0
	mov rcx, rdx
	shr rcx, 32
	mov r8, rdx
	shl r8, 32
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 32
	add r11, r9
	mov rcx, rdx
	shr rcx, 48
	mov r8, rdx
	shl r8, 16
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 16
	add r11, r9
	mov rcx, rdx
	shr rcx, 56
	mov r8, rdx
	shl r8, 8
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 8
	add r11, r9
	mov rcx, rdx
	shr rcx, 60
	mov r8, rdx
	shl r8, 4
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 4
	add r11, r9
	mov rcx, rdx
	shr rcx, 62
	mov r8, rdx
	shl r8, 2
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 2
	add r11, r9
	mov rcx, rdx
	shr rcx, 63
	mov r8, rdx
	shl r8, 1
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 1
	add r11, r9
	mov QWORD PTR [rdi+240], r11
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
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
	mov r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rcx, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2234:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2234b
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
2235:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2235b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rcx, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2236:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2236b
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
2237:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2237b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2238:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2238b
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
	mov eax, 0
	mov r14, 0
2239:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2239b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2240:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2240b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
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
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	mov rax, r12
	add rax, 3
	shl rax, 3
	add rsi, rax
	sub r12, 1
	mov r14, 0
2241:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2241b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	sub r12, 2
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2242:
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
	jne 2242b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	mov rax, r12
	add rax, 3
	mov QWORD PTR [rdi+200], rax
2243:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, r9
	add rbp, rbp
	add rbp, r9
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rdi+200]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	shr r12, 1
	sub r12, 2
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2244:
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
	jne 2244b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2245:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2245b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2246:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2246b
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
	mov rax, QWORD PTR [rdi+200]
	add rcx, r11
	sub rax, 1
	mov QWORD PTR [rbx+rax*8], rcx
	mov QWORD PTR [rdi+200], rax
	jne 2243b
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
2247:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2247b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rcx, QWORD PTR [rdi+240]
	mov r14, 0
2248:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2248b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2249:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2249b
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
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
2250:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2250b
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
2251:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2251b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, rdi
	add r8, 256
	mov r10, r9
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
	mov r14, 0
2252:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2252b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2253:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2253b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r15, -1
	mov ebp, 0
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2254:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2254b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	cmp r12, 65
	jb 2255f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	sub r12, 64
	shl r12, 3
	add rbx, r12
	mov ebp, 0
	mov r12d, 64
	mov r14, 0
2257:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2257b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2258:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2258b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 64
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add rbx, 512
	mov r14, 0
2259:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2259b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2260:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2260b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2261:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2261b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 64
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
	add rbx, 512
	mov r14, 0
2262:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2262b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2263:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2263b
	jmp 2256f
2255:
2256:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	cmp r12, 33
	jb 2264f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	sub r12, 32
	shl r12, 3
	add rbx, r12
	mov ebp, 0
	mov r12d, 32
	mov r14, 0
2266:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2266b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2267:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2267b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 32
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add rbx, 256
	mov r14, 0
2268:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2268b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
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
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2270:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2270b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 32
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
	add rbx, 256
	mov r14, 0
2271:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2271b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2272:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2272b
	jmp 2265f
2264:
2265:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	cmp r12, 17
	jb 2273f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	sub r12, 16
	shl r12, 3
	add rbx, r12
	mov ebp, 0
	mov r12d, 16
	mov r14, 0
2275:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2275b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 16
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add rbx, 128
	mov r14, 0
2277:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2277b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
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
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2279:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2279b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 16
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
	add rbx, 128
	mov r14, 0
2280:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2280b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2281:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2281b
	jmp 2274f
2273:
2274:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	cmp r12, 9
	jb 2282f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	sub r12, 8
	shl r12, 3
	add rbx, r12
	mov ebp, 0
	mov r12d, 8
	mov r14, 0
2284:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2284b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2285:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2285b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 8
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add rbx, 64
	mov r14, 0
2286:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2286b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2287:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2287b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
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
	sub r12, 8
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
	add rbx, 64
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
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2290:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2290b
	jmp 2283f
2282:
2283:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	cmp r12, 5
	jb 2291f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	sub r12, 4
	shl r12, 3
	add rbx, r12
	mov ebp, 0
	mov r12d, 4
	mov r14, 0
2293:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2293b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2294:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2294b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 4
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add rbx, 32
	mov r14, 0
2295:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2295b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2296:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2296b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2297:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2297b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 4
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
	add rbx, 32
	mov r14, 0
2298:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2298b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2299:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2299b
	jmp 2292f
2291:
2292:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	cmp r12, 3
	jb 2300f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	sub r12, 2
	shl r12, 3
	add rbx, r12
	mov ebp, 0
	mov r12d, 2
	mov r14, 0
2302:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2302b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2303:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2303b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add rbx, 16
	mov r14, 0
2304:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2304b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2305:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2305b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2306:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2306b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 2
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
	add rbx, 16
	mov r14, 0
2307:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2307b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2308:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2308b
	jmp 2301f
2300:
2301:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	cmp r12, 2
	jb 2309f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	sub r12, 1
	shl r12, 3
	add rbx, r12
	mov ebp, 0
	mov r12d, 1
	mov r14, 0
2311:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2311b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2312:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2312b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 1
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add rbx, 8
	mov r14, 0
2313:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2313b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2314:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2314b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2315:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2315b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 1
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
	add rbx, 8
	mov r14, 0
2316:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2316b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2317:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2317b
	jmp 2310f
2309:
2310:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov r11d, 0
	mov rcx, rdx
	shr rcx, 32
	mov r8, rdx
	shl r8, 32
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 32
	add r11, r9
	mov rcx, rdx
	shr rcx, 48
	mov r8, rdx
	shl r8, 16
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 16
	add r11, r9
	mov rcx, rdx
	shr rcx, 56
	mov r8, rdx
	shl r8, 8
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 8
	add r11, r9
	mov rcx, rdx
	shr rcx, 60
	mov r8, rdx
	shl r8, 4
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 4
	add r11, r9
	mov rcx, rdx
	shr rcx, 62
	mov r8, rdx
	shl r8, 2
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 2
	add r11, r9
	mov rcx, rdx
	shr rcx, 63
	mov r8, rdx
	shl r8, 1
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 1
	add r11, r9
	mov QWORD PTR [rdi+240], r11
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2318:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2318b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
	mov rcx, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2319:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2319b
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
2320:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2320b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rcx, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2321:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2321b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	add r10, 256
	shr r12, 1
	sub r12, 2
	mov rax, QWORD PTR [r10+r12*8-8]
	movabs rdx, -9223372036854775808
	or rax, rdx
	mov QWORD PTR [r10+r12*8-8], rax
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
2322:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2322b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2323:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2323b
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
	mov eax, 0
	mov r14, 0
2324:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2324b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2325:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2325b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
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
	add rbx, rdi
	add rbx, 256
	shr r12, 1
	sub r12, 2
	mov rax, r12
	add rax, 1
	shl rax, 3
	add rsi, rax
	sub r12, 1
	mov r14, 0
2326:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2326b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	sub r12, 2
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2327:
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
	jne 2327b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	mov rax, r12
	add rax, 1
	mov QWORD PTR [rdi+200], rax
2328:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, r9
	add rbp, rbp
	add rbp, r9
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rdi+200]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	shr r12, 1
	sub r12, 2
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2329:
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
	jne 2329b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2330:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2330b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2331:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2331b
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
	mov rax, QWORD PTR [rdi+200]
	add rcx, r11
	sub rax, 1
	mov QWORD PTR [rbx+rax*8], rcx
	mov QWORD PTR [rdi+200], rax
	jne 2328b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2332:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2332b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2333:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2333b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2334:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2334b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r15, -1
	mov ebp, 0
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2335:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2335b
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
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2336:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2336b
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
2337:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2337b
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
2338:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2338b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2339:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2339b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r15, r9
	add r15, r15
	add r15, r15
	add r15, r15
	add r15, r9
	add r15, rdi
	add r15, 256
	mov r11, QWORD PTR [rdi+160]
	add r11, 7
	shr r11, 3
	mov r13d, 0
	shr r12, 1
	sub r12, 1
2340:
	mov rcx, QWORD PTR [rbx+r13*8]
	mov r8, r13
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r10
	mov r9, r15
	mov ebp, 0
	mov r14, 0
2341:
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
	jne 2341b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r11
	jne 2340b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov ebp, 0
	mov r14, 0
2342:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2342b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov ebp, 0
	mov r14, 0
2343:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2343b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2344:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2344b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2345:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2345b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
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
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2346:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2346b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov eax, 0
	mov QWORD PTR [rbx+r12*8-32], rax
	mov QWORD PTR [rbx+r12*8-24], rax
	mov QWORD PTR [rbx+r12*8-16], rax
	mov QWORD PTR [rbx+r12*8-8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov ebp, 0
	mov r14, 0
2347:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2347b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	cmp rbp, 1
	sbb rbp, rbp
	mov QWORD PTR [rdi+232], rbp
	mov rax, rbp
	and rax, 1
	or rax, QWORD PTR [rbx]
	mov QWORD PTR [rbx], rax
	mov eax, 0
	mov QWORD PTR [rdi+248], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 133
	jb 2348f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, r12
	sub rax, 132
	shl rax, 3
	add rbx, rax
	mov ebp, 0
	mov r12d, 128
	mov r14, 0
2350:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2350b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2351:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2351b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 128
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
	add rbx, rdi
	add rbx, 256
	add rbx, 1024
	mov r14, 0
2352:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2352b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2353:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2353b
	mov rax, QWORD PTR [rdi+216]
	xor rax, -1
	and rax, 128
	add rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	jmp 2349f
2348:
2349:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 69
	jb 2354f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, r12
	sub rax, 68
	shl rax, 3
	add rbx, rax
	mov ebp, 0
	mov r12d, 64
	mov r14, 0
2356:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2356b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2357:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2357b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 64
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
	add rbx, rdi
	add rbx, 256
	add rbx, 512
	mov r14, 0
2358:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2358b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2359:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2359b
	mov rax, QWORD PTR [rdi+216]
	xor rax, -1
	and rax, 64
	add rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	jmp 2355f
2354:
2355:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 37
	jb 2360f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, r12
	sub rax, 36
	shl rax, 3
	add rbx, rax
	mov ebp, 0
	mov r12d, 32
	mov r14, 0
2362:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2362b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2363:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2363b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 32
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
	add rbx, rdi
	add rbx, 256
	add rbx, 256
	mov r14, 0
2364:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2364b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2365:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2365b
	mov rax, QWORD PTR [rdi+216]
	xor rax, -1
	and rax, 32
	add rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	jmp 2361f
2360:
2361:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 21
	jb 2366f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, r12
	sub rax, 20
	shl rax, 3
	add rbx, rax
	mov ebp, 0
	mov r12d, 16
	mov r14, 0
2368:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2368b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2369:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2369b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 16
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
	add rbx, rdi
	add rbx, 256
	add rbx, 128
	mov r14, 0
2370:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2370b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2371:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2371b
	mov rax, QWORD PTR [rdi+216]
	xor rax, -1
	and rax, 16
	add rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	jmp 2367f
2366:
2367:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 13
	jb 2372f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, r12
	sub rax, 12
	shl rax, 3
	add rbx, rax
	mov ebp, 0
	mov r12d, 8
	mov r14, 0
2374:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2374b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2375:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2375b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 8
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
	add rbx, rdi
	add rbx, 256
	add rbx, 64
	mov r14, 0
2376:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2376b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2377:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2377b
	mov rax, QWORD PTR [rdi+216]
	xor rax, -1
	and rax, 8
	add rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	jmp 2373f
2372:
2373:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 9
	jb 2378f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, r12
	sub rax, 8
	shl rax, 3
	add rbx, rax
	mov ebp, 0
	mov r12d, 4
	mov r14, 0
2380:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2380b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2381:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2381b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 4
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
	add rbx, rdi
	add rbx, 256
	add rbx, 32
	mov r14, 0
2382:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2382b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2383:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2383b
	mov rax, QWORD PTR [rdi+216]
	xor rax, -1
	and rax, 4
	add rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	jmp 2379f
2378:
2379:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 7
	jb 2384f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, r12
	sub rax, 6
	shl rax, 3
	add rbx, rax
	mov ebp, 0
	mov r12d, 2
	mov r14, 0
2386:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2386b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2387:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2387b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 2
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
	add rbx, rdi
	add rbx, 256
	add rbx, 16
	mov r14, 0
2388:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2388b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2389:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2389b
	mov rax, QWORD PTR [rdi+216]
	xor rax, -1
	and rax, 2
	add rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	jmp 2385f
2384:
2385:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 6
	jb 2390f
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, r12
	sub rax, 5
	shl rax, 3
	add rbx, rax
	mov ebp, 0
	mov r12d, 1
	mov r14, 0
2392:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2392b
	cmp rbp, 1
	sbb rbp, rbp
	xor rbp, -1
	mov QWORD PTR [rdi+216], rbp
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
2393:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2393b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 1
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
	add rbx, rdi
	add rbx, 256
	add rbx, 8
	mov r14, 0
2394:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2394b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2395:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2395b
	mov rax, QWORD PTR [rdi+216]
	xor rax, -1
	and rax, 1
	add rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	jmp 2391f
2390:
2391:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rdx, QWORD PTR [rbx+r12*8-40]
	mov r11d, 0
	mov rcx, rdx
	shr rcx, 32
	mov r8, rdx
	shl r8, 32
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 32
	add r11, r9
	mov rcx, rdx
	shr rcx, 48
	mov r8, rdx
	shl r8, 16
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 16
	add r11, r9
	mov rcx, rdx
	shr rcx, 56
	mov r8, rdx
	shl r8, 8
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 8
	add r11, r9
	mov rcx, rdx
	shr rcx, 60
	mov r8, rdx
	shl r8, 4
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 4
	add r11, r9
	mov rcx, rdx
	shr rcx, 62
	mov r8, rdx
	shl r8, 2
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 2
	add r11, r9
	mov rcx, rdx
	shr rcx, 63
	mov r8, rdx
	shl r8, 1
	cmp rcx, 1
	cmovb rdx, r8
	sbb r9, r9
	and r9, 1
	add r11, r9
	and r11, -2
	mov QWORD PTR [rdi+240], r11
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	add rsi, rdi
	add rsi, 256
	mov rcx, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [r8]
	shl rax, cl
	mov QWORD PTR [rsi], rax
	mov r14, 1
2396:
	mov rax, QWORD PTR [r8+r14*8]
	shl rax, cl
	mov rdx, QWORD PTR [r8+r14*8-8]
	shr rdx, 1
	xor rcx, 63
	shr rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2396b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
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
2397:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2397b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2398:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2398b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2399:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2399b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2400:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2400b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r8, QWORD PTR [rbx+r12*8-40]
	mov r9, QWORD PTR [rbx+r12*8-48]
	mov r10d, 0
	mov r11d, 0
	mov r13d, 0
	mov ecx, 64
2401:
	shld r11, r13, 2
	shld r13, r8, 2
	shld r8, r9, 2
	shl r9, 2
	mov r14, r10
	shr r14, 62
	mov r15, r10
	shl r15, 2
	or r15, 1
	mov rax, r13
	sub rax, r15
	mov rdx, r11
	sbb rdx, r14
	cmovae r13, rax
	cmovae r11, rdx
	sbb rbx, rbx
	add r10, r10
	add r10, 1
	add r10, rbx
	sub rcx, 1
	jne 2401b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov QWORD PTR [rbx+r12*8-40], r11
	mov QWORD PTR [rbx+r12*8-48], r13
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	shr r12, 1
	sub r12, 2
	mov rax, r10
	add rax, rax
	mov QWORD PTR [rsi+r12*8-8], rax
	mov rax, r10
	shr rax, 63
	mov QWORD PTR [rsi+r12*8], rax
	mov rsi, r9
	add rsi, rdi
	add rsi, 256
	mov QWORD PTR [rsi+16], r10
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov r12d, 3
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2402:
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
	jne 2402b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	shr r12, 1
	sub r12, 2
	sub r12, 1
	mov QWORD PTR [rdi+200], r12
2403:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r11, r9
	add r11, rdi
	add r11, 256
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
	add r10, rdi
	add r10, 256
	shr r12, 1
	sub r12, 2
	mov rcx, QWORD PTR [rdi+200]
	sub rcx, 1
	sub r12, rcx
	add r12, 2
	shl rcx, 3
	add r10, rcx
	add rbx, rcx
	add rbx, rcx
	mov r8, rbx
	mov rax, QWORD PTR [rbx+r12*8-24]
	mov rdx, QWORD PTR [rbx+r12*8-32]
	shld rax, rdx, 63
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov rdx, QWORD PTR [rbx+r12*8-24]
	shld rax, rdx, 63
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rbx+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-16]
	shld rax, rdx, 63
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [r10+r12*8-24]
	mov rdx, QWORD PTR [r10+r12*8-32]
	shld rax, rdx, 63
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [r10+r12*8-16]
	mov rdx, QWORD PTR [r10+r12*8-24]
	shld rax, rdx, 63
	mov QWORD PTR [r11+16], rax
	mov rbx, rsi
	mov r10, r11
	mov rbp, r11
	mov r12d, 3
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
	mov QWORD PTR [rdi+208], rcx
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
	add r10, rdi
	add r10, 256
	shr r12, 1
	sub r12, 2
	mov rcx, QWORD PTR [rdi+200]
	sub rcx, 1
	sub r12, rcx
	add r12, 2
	shl rcx, 3
	add r10, rcx
	add rbx, rcx
	add rbx, rcx
	mov r8, rbx
	mov rcx, QWORD PTR [rdi+208]
	mov QWORD PTR [r10], rcx
	mov r9d, 0
	mov ebp, 0
	mov r14, 0
2404:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2404b
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
	add r10, rdi
	add r10, 256
	shr r12, 1
	sub r12, 2
	mov rcx, QWORD PTR [rdi+200]
	sub rcx, 1
	sub r12, rcx
	add r12, 2
	shl rcx, 3
	add r10, rcx
	add rbx, rcx
	add rbx, rcx
	mov r8, rbx
	mov rax, QWORD PTR [r10]
	add rax, rax
	mov rdx, QWORD PTR [r10+8]
	adc rdx, 0
	sub rax, 1
	sbb rdx, 0
	mov QWORD PTR [r10], rax
	mov QWORD PTR [r10+8], rdx
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
	add r10, rdi
	add r10, 256
	shr r12, 1
	sub r12, 2
	mov rcx, QWORD PTR [rdi+200]
	sub rcx, 1
	sub r12, rcx
	add r12, 2
	shl rcx, 3
	add r10, rcx
	add rbx, rcx
	add rbx, rcx
	mov r8, rbx
	mov rax, QWORD PTR [rbx+r12*8-8]
	add rax, rax
	sbb r15, r15
	mov ebp, 0
	mov r14, 0
2405:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2405b
	mov r11, r15
	and r11, 2
	mov rax, QWORD PTR [r10]
	mov rdx, QWORD PTR [r10+8]
	sub rax, r11
	sbb rdx, 0
	mov QWORD PTR [r10], rax
	mov QWORD PTR [r10+8], rdx
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
	add r10, rdi
	add r10, 256
	shr r12, 1
	sub r12, 2
	mov rcx, QWORD PTR [rdi+200]
	sub rcx, 1
	sub r12, rcx
	add r12, 2
	shl rcx, 3
	add r10, rcx
	add rbx, rcx
	add rbx, rcx
	mov r8, rbx
	mov rax, QWORD PTR [rbx+r12*8-8]
	add rax, rax
	sbb r15, r15
	mov ebp, 0
	mov r14, 0
2406:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2406b
	mov r11, r15
	and r11, 2
	mov rax, QWORD PTR [r10]
	mov rdx, QWORD PTR [r10+8]
	sub rax, r11
	sbb rdx, 0
	mov QWORD PTR [r10], rax
	mov QWORD PTR [r10+8], rdx
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
	add r10, rdi
	add r10, 256
	shr r12, 1
	sub r12, 2
	mov rcx, QWORD PTR [rdi+200]
	sub rcx, 1
	sub r12, rcx
	add r12, 2
	shl rcx, 3
	add r10, rcx
	add rbx, rcx
	add rbx, rcx
	mov r8, rbx
	mov rax, QWORD PTR [rbx+r12*8-8]
	add rax, rax
	sbb r15, r15
	mov ebp, 0
	mov r14, 0
2407:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2407b
	mov r11, r15
	and r11, 2
	mov rax, QWORD PTR [r10]
	mov rdx, QWORD PTR [r10+8]
	sub rax, r11
	sbb rdx, 0
	mov QWORD PTR [r10], rax
	mov QWORD PTR [r10+8], rdx
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
	add r10, rdi
	add r10, 256
	shr r12, 1
	sub r12, 2
	mov rcx, QWORD PTR [rdi+200]
	sub rcx, 1
	sub r12, rcx
	add r12, 2
	shl rcx, 3
	add r10, rcx
	add rbx, rcx
	add rbx, rcx
	mov r8, rbx
	mov rax, QWORD PTR [r10]
	mov rdx, QWORD PTR [r10+8]
	add rax, 1
	adc rdx, 0
	mov QWORD PTR [r10], rax
	mov QWORD PTR [r10+8], rdx
	mov rax, QWORD PTR [rdi+200]
	sub rax, 1
	mov QWORD PTR [rdi+200], rax
	jne 2403b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov ebp, 0
	mov r14, 0
2408:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2408b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2409:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2409b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2410:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, 1
	mov rdx, QWORD PTR [r8+r14*8+8]
	and rdx, 1
	ror rdx, 1
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2410b
	mov rax, QWORD PTR [rdi+248]
	mov rdx, rax
	shr rax, 1
	mov QWORD PTR [rdi+248], rax
	and rdx, 1
	shl rdx, 5
	mov rax, QWORD PTR [rdi+240]
	shr rax, 1
	add rax, rdx
	mov QWORD PTR [rdi+240], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 68
	jb 2411f
	mov rax, QWORD PTR [rdi+248]
	and rax, 64
	cmp rax, 1
	sbb rax, rax
	mov QWORD PTR [rdi+216], rax
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
2413:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2413b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 64
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 512
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2414:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2414b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2415:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2415b
	jmp 2412f
2411:
2412:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 36
	jb 2416f
	mov rax, QWORD PTR [rdi+248]
	and rax, 32
	cmp rax, 1
	sbb rax, rax
	mov QWORD PTR [rdi+216], rax
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
2418:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2418b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 32
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2419:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2419b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2420:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2420b
	jmp 2417f
2416:
2417:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 20
	jb 2421f
	mov rax, QWORD PTR [rdi+248]
	and rax, 16
	cmp rax, 1
	sbb rax, rax
	mov QWORD PTR [rdi+216], rax
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
2423:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2423b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 16
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 128
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2424:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2424b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2425:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2425b
	jmp 2422f
2421:
2422:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 12
	jb 2426f
	mov rax, QWORD PTR [rdi+248]
	and rax, 8
	cmp rax, 1
	sbb rax, rax
	mov QWORD PTR [rdi+216], rax
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
2428:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2428b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 8
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 64
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2429:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2429b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2430:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2430b
	jmp 2427f
2426:
2427:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 8
	jb 2431f
	mov rax, QWORD PTR [rdi+248]
	and rax, 4
	cmp rax, 1
	sbb rax, rax
	mov QWORD PTR [rdi+216], rax
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
2433:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2433b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 4
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 32
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2434:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2434b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2435:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2435b
	jmp 2432f
2431:
2432:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 6
	jb 2436f
	mov rax, QWORD PTR [rdi+248]
	and rax, 2
	cmp rax, 1
	sbb rax, rax
	mov QWORD PTR [rdi+216], rax
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
2438:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2438b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 2
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 16
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2439:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2439b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2440:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2440b
	jmp 2437f
2436:
2437:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	cmp r12, 5
	jb 2441f
	mov rax, QWORD PTR [rdi+248]
	and rax, 1
	cmp rax, 1
	sbb rax, rax
	mov QWORD PTR [rdi+216], rax
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
2443:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2443b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	sub r12, 1
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	add rsi, 8
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2444:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2444b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+216]
	mov r14, 0
2445:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2445b
	jmp 2442f
2441:
2442:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rcx, QWORD PTR [rdi+240]
	mov r14, 0
2446:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, cl
	mov rdx, QWORD PTR [r8+r14*8+8]
	shl rdx, 1
	xor rcx, 63
	shl rdx, cl
	xor rcx, 63
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2446b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2447:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2447b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rdi+232]
	and rax, 1
	mov rdx, QWORD PTR [rbx]
	sub rdx, rax
	mov QWORD PTR [rbx], rdx
	mov r12, QWORD PTR [rdi+144]
	add r12, 7
	shr r12, 3
	add r12, 1
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
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2448:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2448b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r15, -1
	mov ebp, 0
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2449:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2449b
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2450:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, 1
	mov rdx, QWORD PTR [r8+r14*8+8]
	and rdx, 1
	ror rdx, 1
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2450b
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
2451:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2451b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2452:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2452b
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
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
2453:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, 1
	mov rdx, QWORD PTR [r8+r14*8+8]
	and rdx, 1
	ror rdx, 1
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2453b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2454:
	mov rbp, rdx
	and rbp, 7
	je 2455f
	jmp 2456f
2455:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2456:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2454b
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
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2457:
	mov rbp, rdx
	and rbp, 7
	je 2458f
	jmp 2459f
2458:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2459:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2457b
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
2460:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2460b
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+144]
	mov eax, 0
2461:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2461b
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
21:
	ret
	.p2align 6

vg_rsa_check_key:
	mov r11, QWORD PTR [rsp+88]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov QWORD PTR [r11+136], rdi
	mov QWORD PTR [r11+144], rsi
	mov QWORD PTR [r11+152], rdx
	mov QWORD PTR [r11+160], rcx
	mov QWORD PTR [r11+128], r8
	mov QWORD PTR [r11+168], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [r11+232], rax
	mov rdi, r11
	mov r8, rdx
	mov r9, rcx
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
	mov QWORD PTR [rdi+240], r11
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
	jne 23f
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
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
28:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 28b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+224], rax
	mov eax, 0
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
29:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 29b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+168]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
210:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 211f
	jmp 212f
211:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
212:
	test rdx, rdx
	jne 210b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
213:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 213b
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
214:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 214b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+184]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
215:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 216f
	jmp 217f
216:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
217:
	test rdx, rdx
	jne 215b
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
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+208]
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
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 222b
	mov r11, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+192]
	add r10, 7
	shr r10, 3
	mov r9, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+208]
	add r12, 7
	shr r12, 3
	mov r8, QWORD PTR [rdi+80]
	mov r13d, 0
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
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 223b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+80]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
225:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 225b
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	add rbx, rax
	add r12, 2
	mov r14, 0
226:
	mov rax, QWORD PTR [rbx+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 226b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r12, QWORD PTR [rdi+48]
	mov rdx, QWORD PTR [rdi+136]
	mov rax, r12
	and rax, 1
	mov rcx, r12
	shl rcx, 3
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+192]
	shl rcx, 1
	xor rcx, QWORD PTR [rdi+144]
	or rax, rcx
	mov rcx, QWORD PTR [rdi+192]
	xor rcx, QWORD PTR [rdi+208]
	or rax, rcx
	movzx ecx, BYTE PTR [rdx]
	shr rcx, 7
	xor rcx, 1
	or rax, rcx
	je 227f
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
229:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 229b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+184]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+96]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
230:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 231f
	jmp 232f
231:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
232:
	test rdx, rdx
	jne 230b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	sub rbp, 1
	mov r14, 0
233:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 233b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
234:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 234b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+216]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
235:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 236f
	jmp 237f
236:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
237:
	test rdx, rdx
	jne 235b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
238:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 238b
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
239:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 239b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+168]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
240:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 241f
	jmp 242f
241:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
242:
	test rdx, rdx
	jne 240b
	mov r8, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
243:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 243b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
244:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 244b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rcx, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rdi+72]
	mov r8, QWORD PTR [rdi+80]
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
	mov r8, QWORD PTR [rdi+112]
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
	mov r12, QWORD PTR [rdi+192]
	add r12, 7
	shr r12, 3
	mov r13, QWORD PTR [rdi+208]
	add r13, 7
	shr r13, 3
	add r13, 1
	mov rax, r13
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
247:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 247b
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov r8, QWORD PTR [rdi+72]
	mov rsi, QWORD PTR [rdi+104]
	mov r9, QWORD PTR [rdi+80]
248:
	sub r13, 1
	mov r15, QWORD PTR [r9+r13*8]
	mov r11d, 64
249:
	mov rax, r15
	add rax, rax
	mov r15, rax
	sbb rbp, rbp
	mov edx, 0
	mov r14, 0
250:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add rdx, rdx
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rdx, rdx
	add r14, 1
	cmp r14, r12
	jne 250b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	add rdx, rdx
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
251:
	mov rax, QWORD PTR [r8+r14*8]
	test rbp, rbp
	cmove rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
	sub r11, 1
	jne 249b
	test r13, r13
	jne 248b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+120]
	mov ebp, 0
	mov r14, 0
252:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 252b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
253:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 253b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+216]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
254:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 255f
	jmp 256f
255:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
256:
	test rdx, rdx
	jne 254b
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
257:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 257b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rcx, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rdi+72]
	mov r8, QWORD PTR [rdi+80]
	mov ebp, 0
	mov r14, 0
258:
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
	jne 258b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
259:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 259b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+192]
	add r12, 7
	shr r12, 3
	mov r13d, 1
	mov rax, r13
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
260:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 260b
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov r8, QWORD PTR [rdi+72]
	mov rsi, QWORD PTR [rdi+104]
	mov r9, QWORD PTR [rdi+80]
261:
	sub r13, 1
	mov r15, QWORD PTR [r9+r13*8]
	mov r11d, 64
262:
	mov rax, r15
	add rax, rax
	mov r15, rax
	sbb rbp, rbp
	mov edx, 0
	mov r14, 0
263:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add rdx, rdx
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rdx, rdx
	add r14, 1
	cmp r14, r12
	jne 263b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	add rdx, rdx
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
264:
	mov rax, QWORD PTR [r8+r14*8]
	test rbp, rbp
	cmove rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	sub r11, 1
	jne 262b
	test r13, r13
	jne 261b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+120]
	mov ebp, 0
	mov r14, 0
265:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 265b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
266:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 266b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+96]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
267:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 268f
	jmp 269f
268:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
269:
	test rdx, rdx
	jne 267b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	sub rbp, 1
	mov r14, 0
270:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 270b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
271:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+248]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
272:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 273f
	jmp 274f
273:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
274:
	test rdx, rdx
	jne 272b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
275:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 275b
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
276:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 276b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+168]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
277:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 278f
	jmp 279f
278:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
279:
	test rdx, rdx
	jne 277b
	mov r8, QWORD PTR [rdi+88]
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
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
281:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 281b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rcx, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rdi+72]
	mov r8, QWORD PTR [rdi+80]
	mov ebp, 0
	mov r14, 0
282:
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
	jne 282b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
283:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+208]
	add r12, 7
	shr r12, 3
	mov r13, QWORD PTR [rdi+192]
	add r13, 7
	shr r13, 3
	add r13, 1
	mov rax, r13
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
284:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 284b
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov r8, QWORD PTR [rdi+72]
	mov rsi, QWORD PTR [rdi+104]
	mov r9, QWORD PTR [rdi+80]
285:
	sub r13, 1
	mov r15, QWORD PTR [r9+r13*8]
	mov r11d, 64
286:
	mov rax, r15
	add rax, rax
	mov r15, rax
	sbb rbp, rbp
	mov edx, 0
	mov r14, 0
287:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add rdx, rdx
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rdx, rdx
	add r14, 1
	cmp r14, r12
	jne 287b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	add rdx, rdx
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
288:
	mov rax, QWORD PTR [r8+r14*8]
	test rbp, rbp
	cmove rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 288b
	sub r11, 1
	jne 286b
	test r13, r13
	jne 285b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+120]
	mov ebp, 0
	mov r14, 0
289:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 289b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
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
	mov rsi, QWORD PTR [rdi+248]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
291:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 292f
	jmp 293f
292:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
293:
	test rdx, rdx
	jne 291b
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
294:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 294b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rcx, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rdi+72]
	mov r8, QWORD PTR [rdi+80]
	mov ebp, 0
	mov r14, 0
295:
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
	jne 295b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+208]
	add r12, 7
	shr r12, 3
	mov r13d, 1
	mov rax, r13
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
297:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov r8, QWORD PTR [rdi+72]
	mov rsi, QWORD PTR [rdi+104]
	mov r9, QWORD PTR [rdi+80]
298:
	sub r13, 1
	mov r15, QWORD PTR [r9+r13*8]
	mov r11d, 64
299:
	mov rax, r15
	add rax, rax
	mov r15, rax
	sbb rbp, rbp
	mov edx, 0
	mov r14, 0
2100:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add rdx, rdx
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rdx, rdx
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	add rdx, rdx
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2101:
	mov rax, QWORD PTR [r8+r14*8]
	test rbp, rbp
	cmove rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2101b
	sub r11, 1
	jne 299b
	test r13, r13
	jne 298b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+120]
	mov ebp, 0
	mov r14, 0
2102:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2102b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2103:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+184]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+96]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2104:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2105f
	jmp 2106f
2105:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2106:
	test rdx, rdx
	jne 2104b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2107:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+232]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2108:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2109f
	jmp 2110f
2109:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2110:
	test rdx, rdx
	jne 2108b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2111:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2111b
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2112:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+112]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2113:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2114f
	jmp 2115f
2114:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2115:
	test rdx, rdx
	jne 2113b
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2116:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2116b
	mov r11, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+192]
	add r10, 7
	shr r10, 3
	mov r9, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+208]
	add r12, 7
	shr r12, 3
	mov r8, QWORD PTR [rdi+80]
	mov r13d, 0
2117:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2118:
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
	jne 2118b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 2117b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2119:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+192]
	add r12, 7
	shr r12, 3
	mov r13, QWORD PTR [rdi+208]
	add r13, 7
	shr r13, 3
	mov rax, r13
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2120:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov r8, QWORD PTR [rdi+72]
	mov rsi, QWORD PTR [rdi+104]
	mov r9, QWORD PTR [rdi+80]
2121:
	sub r13, 1
	mov r15, QWORD PTR [r9+r13*8]
	mov r11d, 64
2122:
	mov rax, r15
	add rax, rax
	mov r15, rax
	sbb rbp, rbp
	mov edx, 0
	mov r14, 0
2123:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add rdx, rdx
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rdx, rdx
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	add rdx, rdx
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2124:
	mov rax, QWORD PTR [r8+r14*8]
	test rbp, rbp
	cmove rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2124b
	sub r11, 1
	jne 2122b
	test r13, r13
	jne 2121b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+120]
	mov ebp, 0
	mov r14, 0
2125:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2125b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	jmp 228f
227:
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
	mov rsi, QWORD PTR [rdi+184]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+96]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2127:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2128f
	jmp 2129f
2128:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2129:
	test rdx, rdx
	jne 2127b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	sub rbp, 1
	mov r14, 0
2130:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2130b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2131:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2131b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+216]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2132:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2133f
	jmp 2134f
2133:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2134:
	test rdx, rdx
	jne 2132b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2135:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2135b
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
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
2136:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2136b
	mov r8, QWORD PTR [rdi+104]
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
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+168]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2138:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2139f
	jmp 2140f
2139:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2140:
	test rdx, rdx
	jne 2138b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	shr r12, 1
	mov rax, QWORD PTR [r10+r12*8-8]
	movabs rdx, -9223372036854775808
	or rax, rdx
	mov QWORD PTR [r10+r12*8-8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2141:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2141b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	shl rax, 3
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, rax
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	sub r12, 1
	mov r14, 0
2142:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2142b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2143:
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
	jne 2143b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	mov QWORD PTR [rbp+16], rax
2144:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rbp+16]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2145:
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
	jne 2145b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2146:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2146b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2147:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2147b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, QWORD PTR [rbp+16]
	sub rax, 1
	mov QWORD PTR [rbp+16], rax
	jne 2144b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2148:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2148b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+80]
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
	mov rcx, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rdi+72]
	mov r8, QWORD PTR [rdi+80]
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
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2151:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2151b
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
2152:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	shr r12, 1
	mov rax, QWORD PTR [r10+r12*8-8]
	movabs rdx, -9223372036854775808
	or rax, rdx
	mov QWORD PTR [r10+r12*8-8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2153:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2153b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov eax, 2
	shr r12, 1
	shl rax, 3
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, rax
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	sub r12, 1
	mov r14, 0
2154:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2154b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2155:
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
	jne 2155b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov eax, 2
	shr r12, 1
	mov QWORD PTR [rbp+16], rax
2156:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rbp+16]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2157:
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
	jne 2157b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2158:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2158b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2159:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, QWORD PTR [rbp+16]
	sub rax, 1
	mov QWORD PTR [rbp+16], rax
	jne 2156b
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2160:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2160b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2161:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+96]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2162:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2163f
	jmp 2164f
2163:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2164:
	test rdx, rdx
	jne 2162b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	sub rbp, 1
	mov r14, 0
2165:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2165b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2166:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2166b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+248]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2167:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2168f
	jmp 2169f
2168:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2169:
	test rdx, rdx
	jne 2167b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2170:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2170b
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
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
2171:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov r8, QWORD PTR [rdi+104]
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
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+168]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2173:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2174f
	jmp 2175f
2174:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2175:
	test rdx, rdx
	jne 2173b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	shr r12, 1
	mov rax, QWORD PTR [r10+r12*8-8]
	movabs rdx, -9223372036854775808
	or rax, rdx
	mov QWORD PTR [r10+r12*8-8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
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
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	shl rax, 3
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, rax
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	sub r12, 1
	mov r14, 0
2177:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2177b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2178:
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
	jne 2178b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	mov QWORD PTR [rbp+16], rax
2179:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rbp+16]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2180:
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
	jne 2180b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2181:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2182:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, QWORD PTR [rbp+16]
	sub rax, 1
	mov QWORD PTR [rbp+16], rax
	jne 2179b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2183:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2184:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2184b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rcx, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rdi+72]
	mov r8, QWORD PTR [rdi+80]
	mov ebp, 0
	mov r14, 0
2185:
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
	jne 2185b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
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
2187:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2187b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	shr r12, 1
	mov rax, QWORD PTR [r10+r12*8-8]
	movabs rdx, -9223372036854775808
	or rax, rdx
	mov QWORD PTR [r10+r12*8-8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2188:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2188b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov eax, 2
	shr r12, 1
	shl rax, 3
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, rax
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	sub r12, 1
	mov r14, 0
2189:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2189b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2190:
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
	jne 2190b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov eax, 2
	shr r12, 1
	mov QWORD PTR [rbp+16], rax
2191:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rbp+16]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2192:
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
	jne 2192b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2193:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2193b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2194:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2194b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, QWORD PTR [rbp+16]
	sub rax, 1
	mov QWORD PTR [rbp+16], rax
	jne 2191b
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2195:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2195b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2196:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2196b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+184]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+96]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2197:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2198f
	jmp 2199f
2198:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2199:
	test rdx, rdx
	jne 2197b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2200:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2200b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+232]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2201:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2202f
	jmp 2203f
2202:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2203:
	test rdx, rdx
	jne 2201b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2204:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2204b
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+112]
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
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+112]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2206:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2207f
	jmp 2208f
2207:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2208:
	test rdx, rdx
	jne 2206b
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2209:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2209b
	mov r11, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+192]
	add r10, 7
	shr r10, 3
	mov r9, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+208]
	add r12, 7
	shr r12, 3
	mov r8, QWORD PTR [rdi+80]
	mov r13d, 0
2210:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2211:
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
	jne 2211b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 2210b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2212:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2212b
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
2213:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2213b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	shr r12, 1
	mov rax, QWORD PTR [r10+r12*8-8]
	movabs rdx, -9223372036854775808
	or rax, rdx
	mov QWORD PTR [r10+r12*8-8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
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
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	shl rax, 3
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	add rsi, rax
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	sub r12, 1
	mov r14, 0
2215:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2215b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2216:
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
	jne 2216b
	mov QWORD PTR [r8], rcx
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, r12
	shr r12, 1
	sub rax, r12
	add rax, 1
	mov QWORD PTR [rbp+16], rax
2217:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov r11, r9
	add r11, r11
	add r11, r11
	add r11, r9
	add r11, rdi
	add r11, 256
	mov rcx, QWORD PTR [rbp+16]
	sub rcx, 1
	mov rdx, QWORD PTR [r11+rcx*8]
	mov QWORD PTR [rbp+8], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r9
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	shr r12, 1
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
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2218:
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
	jne 2218b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2219:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2219b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2220:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2220b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbp, r9
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rbp
	add rbp, rdi
	add rbp, 256
	mov rax, QWORD PTR [rbp+16]
	sub rax, 1
	mov QWORD PTR [rbp+16], rax
	jne 2217b
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2221:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2221b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
228:
	mov rax, QWORD PTR [rdi+176]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 24f
23:
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
24:
	jmp 22f
21:
	mov eax, 0
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
22:
	ret
	.p2align 6
