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
	mov r10, r12
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
223:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 223b
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
224:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 224b
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
	add r8, r9
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
	add r8, r9
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
	add r8, r9
	add r8, r8
	add r8, r8
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
	add r8, r9
	add r8, r8
	add r8, r8
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
230:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 230b
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
231:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 231b
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
233:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 233b
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
234:
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
235:
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
	jne 235b
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
236:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 236b
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
237:
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
	jne 237b
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
238:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 238b
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
239:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 239b
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
240:
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
	jne 240b
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
241:
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
	jne 241b
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
242:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
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
243:
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
	jne 243b
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
244:
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
	jne 244b
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
245:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 245b
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
246:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 246b
	sub rsi, 1
	jne 234b
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
247:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 247b
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
248:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 248b
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
251:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 251b
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
252:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 252b
	mov r11, r13
	shl r11, 4
	sub r11, r13
	add r11, 10
253:
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
254:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 254b
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
255:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 255b
	mov r14, 0
256:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 256b
	sub r11, 1
	jne 253b
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
257:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 257b
	mov r14, 0
258:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
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
260:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 260b
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
261:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 261b
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
263:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
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
264:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
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
265:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 265b
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
266:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 266b
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
	je 267f
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
269:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 269b
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
270:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 270b
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
271:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
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
272:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 272b
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
273:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 273b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
274:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
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
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
276:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 276b
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
277:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 277b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
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
	jne 274b
	jmp 268f
267:
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
279:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
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
280:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 280b
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
281:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 281b
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
282:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 282b
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
283:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
284:
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
	jne 284b
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
	mov QWORD PTR [rbp+16], rax
285:
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
286:
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
	jne 286b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
287:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 287b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
288:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 288b
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
	jne 285b
268:
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
290:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 290b
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
	je 291f
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
294:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 294b
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
295:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 295b
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
296:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
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
297:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
298:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
299:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 299b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
2100:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2100b
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
2101:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2101b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
2102:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2102b
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
	jne 298b
	jmp 292f
291:
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
2103:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
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
2104:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
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
2105:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2105b
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
2106:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
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
2107:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2108:
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
	jne 2108b
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
	mov QWORD PTR [rbp+16], rax
2109:
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
2110:
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
	jne 2110b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2111:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2112:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2112b
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
	jne 2109b
292:
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
2113:
	mov rbp, rdx
	and rbp, 7
	je 2114f
	jmp 2115f
2114:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2115:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2113b
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
2116:
	mov rbp, rdx
	and rbp, 7
	je 2117f
	jmp 2118f
2117:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2118:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2116b
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
2119:
	mov rbp, rdx
	and rbp, 7
	je 2120f
	jmp 2121f
2120:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2121:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2119b
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
2122:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2122b
	mov rsi, QWORD PTR [rdi+152]
	mov rcx, QWORD PTR [rdi+184]
	mov eax, 0
2123:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2123b
	mov rsi, QWORD PTR [rdi+160]
	mov rcx, QWORD PTR [rdi+168]
	mov eax, 0
2124:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2124b
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
	mov rax, r12
	shl rax, 6
	mov QWORD PTR [rdi+200], rax
228:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+208], rdx
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	and rax, 1
	mov ecx, 0
	sub rcx, rax
	or rcx, rdx
	xor rcx, -1
	mov QWORD PTR [rdi+216], rcx
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
	mov r14, 0
229:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, 1
	mov rdx, QWORD PTR [r8+r14*8+8]
	and rdx, 1
	ror rdx, 1
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 229b
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
	mov rbp, QWORD PTR [rdi+208]
	mov r14, 0
230:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 230b
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
	xor rbp, -1
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
	add r12, r12
	add r12, 2
	mov r15, QWORD PTR [rdi+216]
	mov ebp, 0
	mov r10, r9
	add r10, r10
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
233:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 233b
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
	mov ebp, 0
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
	mov rax, QWORD PTR [rdi+200]
	sub rax, 1
	mov QWORD PTR [rdi+200], rax
	jne 228b
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
235:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 235b
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
236:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 236b
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
237:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 237b
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
238:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 238b
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
239:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 239b
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
240:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 240b
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
241:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 241b
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
242:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
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
243:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 243b
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
244:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 244b
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
245:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 245b
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
246:
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
247:
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
	jne 247b
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
248:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 248b
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
249:
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
	jne 249b
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
250:
	mov rax, QWORD PTR [rbx+r14*8]
	shr rax, 59
	mov r8, QWORD PTR [rbx+r14*8+8]
	shl r8, 5
	add rax, r8
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
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
251:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
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
252:
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
	jne 252b
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
253:
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
	jne 253b
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
254:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
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
255:
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
	jne 255b
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
	mov r9, r13
	mov rax, QWORD PTR [r8+r15*8+8]
	add rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r8+r15*8+8], rax
	add r12, 1
	mov r14, 0
257:
	mov rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [r11+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 257b
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
258:
	mov rax, QWORD PTR [rbx+r14*8]
	mov QWORD PTR [r10+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
	sub rsi, 1
	jne 246b
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
259:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 259b
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
260:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 260b
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
261:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 261b
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
263:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 263b
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
264:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	mov r11, r13
	shl r11, 4
	sub r11, r13
	add r11, 10
265:
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
266:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 266b
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
267:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 267b
	mov r14, 0
268:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 268b
	sub r11, 1
	jne 265b
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
269:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 269b
	mov r14, 0
270:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 270b
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
271:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
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
275:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 275b
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
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
276:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 276b
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
277:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
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
278:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 278b
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
279:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
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
280:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 280b
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
281:
	mov rcx, QWORD PTR [rbx+r13*8]
	mov r8, r13
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r10
	mov r9, r15
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
	add r13, 1
	cmp r13, r11
	jne 281b
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
283:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
284:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
285:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 285b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
286:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 286b
	sub r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
	add r8, r8
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
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
287:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 287b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
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
	jne 284b
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
	add rsi, r9
	add rsi, rsi
	add rsi, rdi
	add rsi, 256
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
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
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
	add rbx, r9
	add rbx, rbx
	add rbx, r9
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
	add rbx, rdi
	add rbx, 256
	mov r14, 0
291:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 291b
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
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
292:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 292b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r15, -1
	mov ebp, 0
	mov r10, r9
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
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
293:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 293b
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
294:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 294b
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
295:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 295b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, r9
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
296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 296b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
297:
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov r14, 0
298:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 298b
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
299:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 299b
	sub r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r9
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
	add rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
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
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
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
	sub r12, 1
	mov rax, rbp
	add rax, 1
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rdx, QWORD PTR [rbx]
	add rdx, rax
	mov QWORD PTR [rbx], rdx
	add r13, 1
	cmp r13, r11
	jne 297b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
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
2103:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r15, -1
	mov ebp, 0
	mov r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, r9
	add r8, rdi
	add r8, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2104:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2104b
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
2105:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2105b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2106:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2106b
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
	add r8, r8
	add r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2108:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2108b
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
2109:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2109b
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
2110:
	mov rcx, QWORD PTR [rbx+r13*8]
	mov r8, r13
	add r8, r8
	add r8, r8
	add r8, r8
	add r8, r10
	mov r9, r15
	mov ebp, 0
	mov r14, 0
2111:
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
	jne 2111b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r11
	jne 2110b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov ebp, 0
	mov r14, 0
2112:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov ebp, 0
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
2114:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2114b
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
2115:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2115b
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
2116:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2116b
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
	mov r8, r9
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
	mov rax, r12
	add rax, 1
	shl rax, 6
	mov QWORD PTR [rdi+200], rax
2119:
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov ebp, 0
	mov r14, 0
2120:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2121:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	add r12, r12
	add r12, 2
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov ebp, 0
	mov r14, 0
2122:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2123:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2123b
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
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2124:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2124b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov ebp, 0
	mov r14, 0
2125:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2125b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rbp, -1
	mov r14, 0
2126:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, r9
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
2127:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2127b
	mov QWORD PTR [rdi+240], rbp
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
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
	add rsi, rdi
	add rsi, 256
	mov rbp, QWORD PTR [rdi+240]
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
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rbp, QWORD PTR [rdi+240]
	xor rbp, -1
	mov r14, 0
2129:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov rax, QWORD PTR [rdi+200]
	sub rax, 1
	mov QWORD PTR [rdi+200], rax
	jne 2119b
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
	add r10, rdi
	add r10, 256
	mov ebp, 0
	mov r14, 0
2130:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2130b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
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
2131:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2131b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r15, -1
	mov ebp, 0
	mov r10, r9
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
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
2132:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r15
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2132b
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
2133:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, 1
	mov rdx, QWORD PTR [r8+r14*8+8]
	and rdx, 1
	ror rdx, 1
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2133b
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
2134:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2134b
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
	add r10, r9
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
2135:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2135b
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
2136:
	mov rax, QWORD PTR [r8+r14*8]
	shr rax, 1
	mov rdx, QWORD PTR [r8+r14*8+8]
	and rdx, 1
	ror rdx, 1
	add rax, rdx
	mov QWORD PTR [rsi+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2136b
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
2137:
	mov rbp, rdx
	and rbp, 7
	je 2138f
	jmp 2139f
2138:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2139:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2137b
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
2140:
	mov rbp, rdx
	and rbp, 7
	je 2141f
	jmp 2142f
2141:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2142:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2140b
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
2143:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2143b
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+144]
	mov eax, 0
2144:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2144b
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
	mov r10, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
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
	mov r10, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
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
2142:
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
	jne 2142b
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
	mov QWORD PTR [rbp+16], rax
2143:
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
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2144:
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
	jne 2144b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2145:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2145b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
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
	jne 2143b
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
	mov r8, QWORD PTR [rdi+112]
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
2152:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov r8, QWORD PTR [rdi+72]
	mov rsi, QWORD PTR [rdi+104]
	mov r9, QWORD PTR [rdi+80]
2153:
	sub r13, 1
	mov r15, QWORD PTR [r9+r13*8]
	mov r11d, 64
2154:
	mov rax, r15
	add rax, rax
	mov r15, rax
	sbb rbp, rbp
	mov edx, 0
	mov r14, 0
2155:
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
	jne 2155b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	add rdx, rdx
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2156:
	mov rax, QWORD PTR [r8+r14*8]
	test rbp, rbp
	cmove rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
	sub r11, 1
	jne 2154b
	test r13, r13
	jne 2153b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+120]
	mov ebp, 0
	mov r14, 0
2157:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2158:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2158b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+96]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2159:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2160f
	jmp 2161f
2160:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2161:
	test rdx, rdx
	jne 2159b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+96]
	mov ebp, 0
	sub rbp, 1
	mov r14, 0
2162:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2162b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2163:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2163b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+248]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2164:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2165f
	jmp 2166f
2165:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2166:
	test rdx, rdx
	jne 2164b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2167:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2167b
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
2168:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov r8, QWORD PTR [rdi+104]
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
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+168]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2170:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2171f
	jmp 2172f
2171:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2172:
	test rdx, rdx
	jne 2170b
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
2173:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2173b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2174:
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
	jne 2174b
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
	mov QWORD PTR [rbp+16], rax
2175:
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
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2176:
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
	jne 2176b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2177:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2177b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2178:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2178b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2179:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2179b
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
	jne 2175b
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
2180:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2180b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+80]
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
	mov rcx, QWORD PTR [rdi+240]
	mov r9, QWORD PTR [rdi+72]
	mov r8, QWORD PTR [rdi+80]
	mov ebp, 0
	mov r14, 0
2182:
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
	jne 2182b
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
2183:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
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
2184:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2184b
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+96]
	mov r8, QWORD PTR [rdi+72]
	mov rsi, QWORD PTR [rdi+104]
	mov r9, QWORD PTR [rdi+80]
2185:
	sub r13, 1
	mov r15, QWORD PTR [r9+r13*8]
	mov r11d, 64
2186:
	mov rax, r15
	add rax, rax
	mov r15, rax
	sbb rbp, rbp
	mov edx, 0
	mov r14, 0
2187:
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
	jne 2187b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	add rdx, rdx
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2188:
	mov rax, QWORD PTR [r8+r14*8]
	test rbp, rbp
	cmove rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2188b
	sub r11, 1
	jne 2186b
	test r13, r13
	jne 2185b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+120]
	mov ebp, 0
	mov r14, 0
2189:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2189b
	cmp rbp, 1
	sbb rbp, rbp
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+96]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2190:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2190b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+184]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+96]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2191:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2192f
	jmp 2193f
2192:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2193:
	test rdx, rdx
	jne 2191b
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2194:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2194b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+232]
	mov rcx, QWORD PTR [rdi+192]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2195:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2196f
	jmp 2197f
2196:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2197:
	test rdx, rdx
	jne 2195b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+96]
	mov ebp, 0
	mov r14, 0
2198:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2198b
	and rbp, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rbp
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2199:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2199b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+208]
	mov rbx, QWORD PTR [rdi+112]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2200:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2201f
	jmp 2202f
2201:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2202:
	test rdx, rdx
	jne 2200b
	mov r8, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2203:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2203b
	mov r11, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+80]
	mov r13d, 0
2204:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2205:
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
	jne 2205b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r8, 8
	add r13, 1
	cmp r13, r10
	jne 2204b
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
2206:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2206b
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
2207:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2207b
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
2208:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2208b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
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
2209:
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
	jne 2209b
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
	mov QWORD PTR [rbp+16], rax
2210:
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
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov rdx, QWORD PTR [rbp+8]
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2211:
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
	jne 2211b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2212:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2212b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2213:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2213b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2214:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2214b
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
	jne 2210b
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
2215:
	mov rax, QWORD PTR [rbx+r14*8]
	xor rax, QWORD PTR [r10+r14*8]
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2215b
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
