// The functions of `src/internal/vg_dsa_prime_setup_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_prime_setup_adx:
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
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
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
20:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 20b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 21f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 23f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 25f
27:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 27b
	jmp 26f
25:
26:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
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
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
29:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
210:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 210b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
211:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 211b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
212:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 212b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 29b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
213:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	movdqu xmm3, XMMWORD PTR [rdi+128]
	movdqu xmm4, XMMWORD PTR [rdi+144]
	movdqu xmm5, XMMWORD PTR [rdi+160]
	movdqu xmm6, XMMWORD PTR [rdi+224]
	movdqu xmm7, XMMWORD PTR [rdi+240]
	mov rax, QWORD PTR [rdi+rdx*8+64]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+rcx*8+64]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+r8*8+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+48]
	sub rax, 8
	ror rax, 3
	shr rax, 27
	je 214f
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	mov eax, 0
	mov r14, 0
216:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 216b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
217:
	mov rcx, QWORD PTR [r11+r13*8]
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
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
219:
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
	jne 219b
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
	jne 217b
	mov ebp, 0
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
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
221:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 221b
	jmp 215f
214:
	cmp rcx, r8
	je 222f
	jmp 223f
222:
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
224:
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rbp, QWORD PTR [rdi+136]
	add rbp, rax
	mov rsi, QWORD PTR [rdi+80]
	mov rcx, QWORD PTR [rdi+224]
	shl rcx, 4
	add rcx, rsi
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+136], rax
	mov rdx, QWORD PTR [rbp]
	xor eax, eax
	mulx rbx, r8, QWORD PTR [rbp+8]
	mulx rax, r9, QWORD PTR [rbp+16]
	adcx r9, rbx
	mulx rbx, r10, QWORD PTR [rbp+24]
	adcx r10, rax
	mulx rax, r11, QWORD PTR [rbp+32]
	adcx r11, rbx
	mulx rbx, r12, QWORD PTR [rbp+40]
	adcx r12, rax
	mulx rax, r13, QWORD PTR [rbp+48]
	adcx r13, rbx
	mulx rbx, r14, QWORD PTR [rbp+56]
	adcx r14, rax
	mov r15d, 0
	adcx r15, rbx
	mov QWORD PTR [rcx+24], r8
	mov QWORD PTR [rcx+32], r9
	mov rdx, QWORD PTR [rbp+8]
	xor r8d, r8d
	mulx rbx, rsi, QWORD PTR [rbp+16]
	adcx r10, rsi
	mulx rax, rsi, QWORD PTR [rbp+24]
	adcx r11, rsi
	adox r11, rbx
	mulx rbx, rsi, QWORD PTR [rbp+32]
	adcx r12, rsi
	adox r12, rax
	mulx rax, rsi, QWORD PTR [rbp+40]
	adcx r13, rsi
	adox r13, rbx
	mulx rbx, rsi, QWORD PTR [rbp+48]
	adcx r14, rsi
	adox r14, rax
	mulx rax, rsi, QWORD PTR [rbp+56]
	adcx r15, rsi
	adox r15, rbx
	adcx r8, r8
	adox r8, rax
	mov QWORD PTR [rcx+40], r10
	mov QWORD PTR [rcx+48], r11
	mov rdx, QWORD PTR [rbp+16]
	xor r10d, r10d
	mulx rbx, rsi, QWORD PTR [rbp+24]
	adcx r12, rsi
	mulx rax, rsi, QWORD PTR [rbp+32]
	adcx r13, rsi
	adox r13, rbx
	mulx rbx, rsi, QWORD PTR [rbp+40]
	adcx r14, rsi
	adox r14, rax
	mulx rax, rsi, QWORD PTR [rbp+48]
	adcx r15, rsi
	adox r15, rbx
	mulx rbx, rsi, QWORD PTR [rbp+56]
	adcx r8, rsi
	adox r8, rax
	adcx r10, r10
	adox r10, rbx
	mov QWORD PTR [rcx+56], r12
	mov QWORD PTR [rcx+64], r13
	mov rdx, QWORD PTR [rbp+24]
	xor r12d, r12d
	mulx rbx, rsi, QWORD PTR [rbp+32]
	adcx r14, rsi
	mulx rax, rsi, QWORD PTR [rbp+40]
	adcx r15, rsi
	adox r15, rbx
	mulx rbx, rsi, QWORD PTR [rbp+48]
	adcx r8, rsi
	adox r8, rax
	mulx rax, rsi, QWORD PTR [rbp+56]
	adcx r10, rsi
	adox r10, rbx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [rcx+72], r14
	mov QWORD PTR [rcx+80], r15
	mov rdx, QWORD PTR [rbp+32]
	xor r14d, r14d
	mulx rbx, rsi, QWORD PTR [rbp+40]
	adcx r8, rsi
	mulx rax, rsi, QWORD PTR [rbp+48]
	adcx r10, rsi
	adox r10, rbx
	mulx rbx, rsi, QWORD PTR [rbp+56]
	adcx r12, rsi
	adox r12, rax
	adcx r14, r14
	adox r14, rbx
	mov QWORD PTR [rcx+88], r8
	mov QWORD PTR [rcx+96], r10
	mov rdx, QWORD PTR [rbp+40]
	xor r8d, r8d
	mulx rbx, rsi, QWORD PTR [rbp+48]
	adcx r12, rsi
	mulx rax, rsi, QWORD PTR [rbp+56]
	adcx r14, rsi
	adox r14, rbx
	adcx r8, r8
	adox r8, rax
	mov QWORD PTR [rcx+104], r12
	mov QWORD PTR [rcx+112], r14
	mov rdx, QWORD PTR [rbp+48]
	xor r12d, r12d
	mulx rbx, rsi, QWORD PTR [rbp+56]
	adcx r8, rsi
	adcx r12, r12
	adox r12, rbx
	mov QWORD PTR [rcx+120], r8
	mov QWORD PTR [rcx+128], r12
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 224b
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 8
	je 225f
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 16
	je 227f
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+248], rax
229:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+136]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+136]
	add rbp, rdx
	add rax, rdx
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	add rsi, 16
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 230f
232:
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	mov rdx, QWORD PTR [rdi+240]
	add rsi, 64
	xor eax, eax
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rdi+240], rax
	add rbp, 64
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	jne 232b
	jmp 231f
230:
231:
	mov rax, QWORD PTR [rdi+248]
	add rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	mov rdx, QWORD PTR [rdi+240]
	add rsi, 64
	xor eax, eax
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rdi+240], rax
	add rbp, 64
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	cmp rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov rax, QWORD PTR [rdi+224]
	add rax, 16
	cmp rax, QWORD PTR [rdi+48]
	je 233f
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+248], rax
	jmp 234f
233:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 235f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
237:
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	xor eax, eax
	adcx r8, rbp
	adcx r9, rcx
	adcx r10, rcx
	adcx r11, rcx
	adcx r12, rcx
	adcx r13, rcx
	adcx r14, rcx
	adcx r15, rcx
	mov ebp, 0
	adcx rbp, rax
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	add rsi, 64
	cmp rsi, rdx
	jne 237b
	jmp 236f
235:
236:
234:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 229b
	jmp 228f
227:
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
238:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+136]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+136]
	add rbp, rdx
	add rax, rdx
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	add rsi, 16
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
239:
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	mov rdx, QWORD PTR [rdi+240]
	add rsi, 64
	xor eax, eax
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rdi+240], rax
	add rbp, 64
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 239b
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 240f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
242:
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	xor eax, eax
	adcx r8, rbp
	adcx r9, rcx
	adcx r10, rcx
	adcx r11, rcx
	adcx r12, rcx
	adcx r13, rcx
	adcx r14, rcx
	adcx r15, rcx
	mov ebp, 0
	adcx rbp, rax
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	add rsi, 64
	cmp rsi, rdx
	jne 242b
	jmp 241f
240:
241:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 238b
228:
	jmp 226f
225:
226:
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov eax, 0
	mov QWORD PTR [r9], rax
	mov QWORD PTR [r9+8], rax
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov r10, rbx
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
243:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mulx rax, rcx, rdx
	add rcx, r15
	adc rax, 0
	xor esi, esi
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov rdx, QWORD PTR [r9+rbp*8+8]
	mov r11, QWORD PTR [r8+r14*8+16]
	mov r12, QWORD PTR [r8+r14*8+24]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+16], r11
	mov QWORD PTR [r8+r14*8+24], r12
	mov rdx, QWORD PTR [r9+rbp*8+16]
	mov r11, QWORD PTR [r8+r14*8+32]
	mov r12, QWORD PTR [r8+r14*8+40]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+32], r11
	mov QWORD PTR [r8+r14*8+40], r12
	mov rdx, QWORD PTR [r9+rbp*8+24]
	mov r11, QWORD PTR [r8+r14*8+48]
	mov r12, QWORD PTR [r8+r14*8+56]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+48], r11
	mov QWORD PTR [r8+r14*8+56], r12
	mov rdx, QWORD PTR [r9+rbp*8+32]
	mov r11, QWORD PTR [r8+r14*8+64]
	mov r12, QWORD PTR [r8+r14*8+72]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+64], r11
	mov QWORD PTR [r8+r14*8+72], r12
	mov rdx, QWORD PTR [r9+rbp*8+40]
	mov r11, QWORD PTR [r8+r14*8+80]
	mov r12, QWORD PTR [r8+r14*8+88]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+80], r11
	mov QWORD PTR [r8+r14*8+88], r12
	mov rdx, QWORD PTR [r9+rbp*8+48]
	mov r11, QWORD PTR [r8+r14*8+96]
	mov r12, QWORD PTR [r8+r14*8+104]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+96], r11
	mov QWORD PTR [r8+r14*8+104], r12
	mov rdx, QWORD PTR [r9+rbp*8+56]
	mov r11, QWORD PTR [r8+r14*8+112]
	mov r12, QWORD PTR [r8+r14*8+120]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+112], r11
	mov QWORD PTR [r8+r14*8+120], r12
	mov r15d, 0
	adcx r15, rsi
	adox r15, rsi
	add rbp, 8
	add r14, 16
	cmp rbp, r10
	jne 243b
223:
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
244:
	mov rsi, rcx
	mov rbp, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+8], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+16], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+24], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+32], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+40], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+48], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+56], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov eax, 0
	mov QWORD PTR [rcx-8], rax
	add rbp, 64
	add rsi, 64
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, QWORD PTR [rdi+64]
	cmp rbp, rax
	jne 245f
	jmp 246f
245:
247:
	mov rdx, QWORD PTR [rcx-8]
	add rdx, -1
	adcx r8, QWORD PTR [rsi]
	adcx r9, QWORD PTR [rsi+8]
	adcx r10, QWORD PTR [rsi+16]
	adcx r11, QWORD PTR [rsi+24]
	adcx r12, QWORD PTR [rsi+32]
	adcx r13, QWORD PTR [rsi+40]
	adcx r14, QWORD PTR [rsi+48]
	adcx r15, QWORD PTR [rsi+56]
	mov eax, 0
	adcx rax, rax
	mov QWORD PTR [rcx-8], rax
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	add rbp, 64
	add rsi, 64
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, QWORD PTR [rdi+64]
	cmp rbp, rax
	jne 247b
246:
	mov rdx, QWORD PTR [rcx-8]
	add rdx, -1
	mov eax, 0
	mov rdx, QWORD PTR [rcx-16]
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov QWORD PTR [rcx+48], rax
	add rcx, 64
	cmp rcx, QWORD PTR [rdi+88]
	jne 244b
	mov r8, rcx
	mov rbp, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rcx-16]
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+128]
	mov ebp, 0
	mov r14, 0
248:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	mov rax, QWORD PTR [r8+r14*8+8]
	sbb rax, QWORD PTR [r10+r14*8+8]
	mov QWORD PTR [rsi+r14*8+8], rax
	mov rax, QWORD PTR [r8+r14*8+16]
	sbb rax, QWORD PTR [r10+r14*8+16]
	mov QWORD PTR [rsi+r14*8+16], rax
	mov rax, QWORD PTR [r8+r14*8+24]
	sbb rax, QWORD PTR [r10+r14*8+24]
	mov QWORD PTR [rsi+r14*8+24], rax
	mov rax, QWORD PTR [r8+r14*8+32]
	sbb rax, QWORD PTR [r10+r14*8+32]
	mov QWORD PTR [rsi+r14*8+32], rax
	mov rax, QWORD PTR [r8+r14*8+40]
	sbb rax, QWORD PTR [r10+r14*8+40]
	mov QWORD PTR [rsi+r14*8+40], rax
	mov rax, QWORD PTR [r8+r14*8+48]
	sbb rax, QWORD PTR [r10+r14*8+48]
	mov QWORD PTR [rsi+r14*8+48], rax
	mov rax, QWORD PTR [r8+r14*8+56]
	sbb rax, QWORD PTR [r10+r14*8+56]
	mov QWORD PTR [rsi+r14*8+56], rax
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 248b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
249:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	cmovb rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	mov rax, QWORD PTR [rsi+r14*8+8]
	cmovb rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [rbx+r14*8+8], rax
	mov rax, QWORD PTR [rsi+r14*8+16]
	cmovb rax, QWORD PTR [r8+r14*8+16]
	mov QWORD PTR [rbx+r14*8+16], rax
	mov rax, QWORD PTR [rsi+r14*8+24]
	cmovb rax, QWORD PTR [r8+r14*8+24]
	mov QWORD PTR [rbx+r14*8+24], rax
	mov rax, QWORD PTR [rsi+r14*8+32]
	cmovb rax, QWORD PTR [r8+r14*8+32]
	mov QWORD PTR [rbx+r14*8+32], rax
	mov rax, QWORD PTR [rsi+r14*8+40]
	cmovb rax, QWORD PTR [r8+r14*8+40]
	mov QWORD PTR [rbx+r14*8+40], rax
	mov rax, QWORD PTR [rsi+r14*8+48]
	cmovb rax, QWORD PTR [r8+r14*8+48]
	mov QWORD PTR [rbx+r14*8+48], rax
	mov rax, QWORD PTR [rsi+r14*8+56]
	cmovb rax, QWORD PTR [r8+r14*8+56]
	mov QWORD PTR [rbx+r14*8+56], rax
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 249b
215:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	movdqu XMMWORD PTR [rdi+128], xmm3
	movdqu XMMWORD PTR [rdi+144], xmm4
	movdqu XMMWORD PTR [rdi+160], xmm5
	movdqu XMMWORD PTR [rdi+224], xmm6
	movdqu XMMWORD PTR [rdi+240], xmm7
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 213b
	jmp 24f
23:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
250:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
251:
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
	jne 251b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
252:
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
253:
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
	jne 253b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
254:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
255:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 255b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 252b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
256:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	movdqu xmm3, XMMWORD PTR [rdi+128]
	movdqu xmm4, XMMWORD PTR [rdi+144]
	movdqu xmm5, XMMWORD PTR [rdi+160]
	movdqu xmm6, XMMWORD PTR [rdi+224]
	movdqu xmm7, XMMWORD PTR [rdi+240]
	mov rax, QWORD PTR [rdi+rdx*8+64]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+rcx*8+64]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+r8*8+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+48]
	sub rax, 8
	ror rax, 3
	shr rax, 27
	je 257f
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	mov eax, 0
	mov r14, 0
259:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 259b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
260:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
261:
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
	jne 261b
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
262:
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
	jne 262b
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
	jne 260b
	mov ebp, 0
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
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
264:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	jmp 258f
257:
	cmp rcx, r8
	je 265f
	jmp 266f
265:
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
267:
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rbp, QWORD PTR [rdi+136]
	add rbp, rax
	mov rsi, QWORD PTR [rdi+80]
	mov rcx, QWORD PTR [rdi+224]
	shl rcx, 4
	add rcx, rsi
	mov eax, 0
	mov QWORD PTR [rcx+16], rax
	mov QWORD PTR [rcx+136], rax
	mov rdx, QWORD PTR [rbp]
	xor eax, eax
	mulx rbx, r8, QWORD PTR [rbp+8]
	mulx rax, r9, QWORD PTR [rbp+16]
	adcx r9, rbx
	mulx rbx, r10, QWORD PTR [rbp+24]
	adcx r10, rax
	mulx rax, r11, QWORD PTR [rbp+32]
	adcx r11, rbx
	mulx rbx, r12, QWORD PTR [rbp+40]
	adcx r12, rax
	mulx rax, r13, QWORD PTR [rbp+48]
	adcx r13, rbx
	mulx rbx, r14, QWORD PTR [rbp+56]
	adcx r14, rax
	mov r15d, 0
	adcx r15, rbx
	mov QWORD PTR [rcx+24], r8
	mov QWORD PTR [rcx+32], r9
	mov rdx, QWORD PTR [rbp+8]
	xor r8d, r8d
	mulx rbx, rsi, QWORD PTR [rbp+16]
	adcx r10, rsi
	mulx rax, rsi, QWORD PTR [rbp+24]
	adcx r11, rsi
	adox r11, rbx
	mulx rbx, rsi, QWORD PTR [rbp+32]
	adcx r12, rsi
	adox r12, rax
	mulx rax, rsi, QWORD PTR [rbp+40]
	adcx r13, rsi
	adox r13, rbx
	mulx rbx, rsi, QWORD PTR [rbp+48]
	adcx r14, rsi
	adox r14, rax
	mulx rax, rsi, QWORD PTR [rbp+56]
	adcx r15, rsi
	adox r15, rbx
	adcx r8, r8
	adox r8, rax
	mov QWORD PTR [rcx+40], r10
	mov QWORD PTR [rcx+48], r11
	mov rdx, QWORD PTR [rbp+16]
	xor r10d, r10d
	mulx rbx, rsi, QWORD PTR [rbp+24]
	adcx r12, rsi
	mulx rax, rsi, QWORD PTR [rbp+32]
	adcx r13, rsi
	adox r13, rbx
	mulx rbx, rsi, QWORD PTR [rbp+40]
	adcx r14, rsi
	adox r14, rax
	mulx rax, rsi, QWORD PTR [rbp+48]
	adcx r15, rsi
	adox r15, rbx
	mulx rbx, rsi, QWORD PTR [rbp+56]
	adcx r8, rsi
	adox r8, rax
	adcx r10, r10
	adox r10, rbx
	mov QWORD PTR [rcx+56], r12
	mov QWORD PTR [rcx+64], r13
	mov rdx, QWORD PTR [rbp+24]
	xor r12d, r12d
	mulx rbx, rsi, QWORD PTR [rbp+32]
	adcx r14, rsi
	mulx rax, rsi, QWORD PTR [rbp+40]
	adcx r15, rsi
	adox r15, rbx
	mulx rbx, rsi, QWORD PTR [rbp+48]
	adcx r8, rsi
	adox r8, rax
	mulx rax, rsi, QWORD PTR [rbp+56]
	adcx r10, rsi
	adox r10, rbx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [rcx+72], r14
	mov QWORD PTR [rcx+80], r15
	mov rdx, QWORD PTR [rbp+32]
	xor r14d, r14d
	mulx rbx, rsi, QWORD PTR [rbp+40]
	adcx r8, rsi
	mulx rax, rsi, QWORD PTR [rbp+48]
	adcx r10, rsi
	adox r10, rbx
	mulx rbx, rsi, QWORD PTR [rbp+56]
	adcx r12, rsi
	adox r12, rax
	adcx r14, r14
	adox r14, rbx
	mov QWORD PTR [rcx+88], r8
	mov QWORD PTR [rcx+96], r10
	mov rdx, QWORD PTR [rbp+40]
	xor r8d, r8d
	mulx rbx, rsi, QWORD PTR [rbp+48]
	adcx r12, rsi
	mulx rax, rsi, QWORD PTR [rbp+56]
	adcx r14, rsi
	adox r14, rbx
	adcx r8, r8
	adox r8, rax
	mov QWORD PTR [rcx+104], r12
	mov QWORD PTR [rcx+112], r14
	mov rdx, QWORD PTR [rbp+48]
	xor r12d, r12d
	mulx rbx, rsi, QWORD PTR [rbp+56]
	adcx r8, rsi
	adcx r12, r12
	adox r12, rbx
	mov QWORD PTR [rcx+120], r8
	mov QWORD PTR [rcx+128], r12
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 267b
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 8
	je 268f
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 16
	je 270f
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+248], rax
272:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+136]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+136]
	add rbp, rdx
	add rax, rdx
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	add rsi, 16
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 273f
275:
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	mov rdx, QWORD PTR [rdi+240]
	add rsi, 64
	xor eax, eax
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rdi+240], rax
	add rbp, 64
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	jne 275b
	jmp 274f
273:
274:
	mov rax, QWORD PTR [rdi+248]
	add rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	mov rdx, QWORD PTR [rdi+240]
	add rsi, 64
	xor eax, eax
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rdi+240], rax
	add rbp, 64
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	cmp rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov rax, QWORD PTR [rdi+224]
	add rax, 16
	cmp rax, QWORD PTR [rdi+48]
	je 276f
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+248], rax
	jmp 277f
276:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 278f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
280:
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	xor eax, eax
	adcx r8, rbp
	adcx r9, rcx
	adcx r10, rcx
	adcx r11, rcx
	adcx r12, rcx
	adcx r13, rcx
	adcx r14, rcx
	adcx r15, rcx
	mov ebp, 0
	adcx rbp, rax
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	add rsi, 64
	cmp rsi, rdx
	jne 280b
	jmp 279f
278:
279:
277:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 272b
	jmp 271f
270:
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
281:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+136]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+136]
	add rbp, rdx
	add rax, rdx
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	add rsi, 16
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
282:
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	mov rdx, QWORD PTR [rdi+240]
	add rsi, 64
	xor eax, eax
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rdi+240], rax
	add rbp, 64
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 282b
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 283f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
285:
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	xor eax, eax
	adcx r8, rbp
	adcx r9, rcx
	adcx r10, rcx
	adcx r11, rcx
	adcx r12, rcx
	adcx r13, rcx
	adcx r14, rcx
	adcx r15, rcx
	mov ebp, 0
	adcx rbp, rax
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	add rsi, 64
	cmp rsi, rdx
	jne 285b
	jmp 284f
283:
284:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 281b
271:
	jmp 269f
268:
269:
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov eax, 0
	mov QWORD PTR [r9], rax
	mov QWORD PTR [r9+8], rax
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov r10, rbx
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
286:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mulx rax, rcx, rdx
	add rcx, r15
	adc rax, 0
	xor esi, esi
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov rdx, QWORD PTR [r9+rbp*8+8]
	mov r11, QWORD PTR [r8+r14*8+16]
	mov r12, QWORD PTR [r8+r14*8+24]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+16], r11
	mov QWORD PTR [r8+r14*8+24], r12
	mov rdx, QWORD PTR [r9+rbp*8+16]
	mov r11, QWORD PTR [r8+r14*8+32]
	mov r12, QWORD PTR [r8+r14*8+40]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+32], r11
	mov QWORD PTR [r8+r14*8+40], r12
	mov rdx, QWORD PTR [r9+rbp*8+24]
	mov r11, QWORD PTR [r8+r14*8+48]
	mov r12, QWORD PTR [r8+r14*8+56]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+48], r11
	mov QWORD PTR [r8+r14*8+56], r12
	mov rdx, QWORD PTR [r9+rbp*8+32]
	mov r11, QWORD PTR [r8+r14*8+64]
	mov r12, QWORD PTR [r8+r14*8+72]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+64], r11
	mov QWORD PTR [r8+r14*8+72], r12
	mov rdx, QWORD PTR [r9+rbp*8+40]
	mov r11, QWORD PTR [r8+r14*8+80]
	mov r12, QWORD PTR [r8+r14*8+88]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+80], r11
	mov QWORD PTR [r8+r14*8+88], r12
	mov rdx, QWORD PTR [r9+rbp*8+48]
	mov r11, QWORD PTR [r8+r14*8+96]
	mov r12, QWORD PTR [r8+r14*8+104]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+96], r11
	mov QWORD PTR [r8+r14*8+104], r12
	mov rdx, QWORD PTR [r9+rbp*8+56]
	mov r11, QWORD PTR [r8+r14*8+112]
	mov r12, QWORD PTR [r8+r14*8+120]
	mulx rax, rcx, rdx
	adcx r11, r11
	adox r11, rcx
	adcx r12, r12
	adox r12, rax
	mov QWORD PTR [r8+r14*8+112], r11
	mov QWORD PTR [r8+r14*8+120], r12
	mov r15d, 0
	adcx r15, rsi
	adox r15, rsi
	add rbp, 8
	add r14, 16
	cmp rbp, r10
	jne 286b
266:
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
287:
	mov rsi, rcx
	mov rbp, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+8], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+16], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+24], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+32], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+40], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+48], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+56], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov eax, 0
	mov QWORD PTR [rcx-8], rax
	add rbp, 64
	add rsi, 64
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, QWORD PTR [rdi+64]
	cmp rbp, rax
	jne 288f
	jmp 289f
288:
290:
	mov rdx, QWORD PTR [rcx-8]
	add rdx, -1
	adcx r8, QWORD PTR [rsi]
	adcx r9, QWORD PTR [rsi+8]
	adcx r10, QWORD PTR [rsi+16]
	adcx r11, QWORD PTR [rsi+24]
	adcx r12, QWORD PTR [rsi+32]
	adcx r13, QWORD PTR [rsi+40]
	adcx r14, QWORD PTR [rsi+48]
	adcx r15, QWORD PTR [rsi+56]
	mov eax, 0
	adcx rax, rax
	mov QWORD PTR [rcx-8], rax
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	add rbp, 64
	add rsi, 64
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, QWORD PTR [rdi+64]
	cmp rbp, rax
	jne 290b
289:
	mov rdx, QWORD PTR [rcx-8]
	add rdx, -1
	mov eax, 0
	mov rdx, QWORD PTR [rcx-16]
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov QWORD PTR [rcx+48], rax
	add rcx, 64
	cmp rcx, QWORD PTR [rdi+88]
	jne 287b
	mov r8, rcx
	mov rbp, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rcx-16]
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+128]
	mov ebp, 0
	mov r14, 0
291:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	mov rax, QWORD PTR [r8+r14*8+8]
	sbb rax, QWORD PTR [r10+r14*8+8]
	mov QWORD PTR [rsi+r14*8+8], rax
	mov rax, QWORD PTR [r8+r14*8+16]
	sbb rax, QWORD PTR [r10+r14*8+16]
	mov QWORD PTR [rsi+r14*8+16], rax
	mov rax, QWORD PTR [r8+r14*8+24]
	sbb rax, QWORD PTR [r10+r14*8+24]
	mov QWORD PTR [rsi+r14*8+24], rax
	mov rax, QWORD PTR [r8+r14*8+32]
	sbb rax, QWORD PTR [r10+r14*8+32]
	mov QWORD PTR [rsi+r14*8+32], rax
	mov rax, QWORD PTR [r8+r14*8+40]
	sbb rax, QWORD PTR [r10+r14*8+40]
	mov QWORD PTR [rsi+r14*8+40], rax
	mov rax, QWORD PTR [r8+r14*8+48]
	sbb rax, QWORD PTR [r10+r14*8+48]
	mov QWORD PTR [rsi+r14*8+48], rax
	mov rax, QWORD PTR [r8+r14*8+56]
	sbb rax, QWORD PTR [r10+r14*8+56]
	mov QWORD PTR [rsi+r14*8+56], rax
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 291b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
292:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	cmovb rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	mov rax, QWORD PTR [rsi+r14*8+8]
	cmovb rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [rbx+r14*8+8], rax
	mov rax, QWORD PTR [rsi+r14*8+16]
	cmovb rax, QWORD PTR [r8+r14*8+16]
	mov QWORD PTR [rbx+r14*8+16], rax
	mov rax, QWORD PTR [rsi+r14*8+24]
	cmovb rax, QWORD PTR [r8+r14*8+24]
	mov QWORD PTR [rbx+r14*8+24], rax
	mov rax, QWORD PTR [rsi+r14*8+32]
	cmovb rax, QWORD PTR [r8+r14*8+32]
	mov QWORD PTR [rbx+r14*8+32], rax
	mov rax, QWORD PTR [rsi+r14*8+40]
	cmovb rax, QWORD PTR [r8+r14*8+40]
	mov QWORD PTR [rbx+r14*8+40], rax
	mov rax, QWORD PTR [rsi+r14*8+48]
	cmovb rax, QWORD PTR [r8+r14*8+48]
	mov QWORD PTR [rbx+r14*8+48], rax
	mov rax, QWORD PTR [rsi+r14*8+56]
	cmovb rax, QWORD PTR [r8+r14*8+56]
	mov QWORD PTR [rbx+r14*8+56], rax
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 292b
258:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	movdqu XMMWORD PTR [rdi+128], xmm3
	movdqu XMMWORD PTR [rdi+144], xmm4
	movdqu XMMWORD PTR [rdi+160], xmm5
	movdqu XMMWORD PTR [rdi+224], xmm6
	movdqu XMMWORD PTR [rdi+240], xmm7
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 256b
24:
	jmp 22f
21:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
293:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 293b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
294:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
295:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 295b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
296:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 296b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
297:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 297b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 294b
22:
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	movdqu xmm3, XMMWORD PTR [rdi+128]
	movdqu xmm4, XMMWORD PTR [rdi+144]
	movdqu xmm5, XMMWORD PTR [rdi+160]
	movdqu xmm6, XMMWORD PTR [rdi+224]
	movdqu xmm7, XMMWORD PTR [rdi+240]
	mov rax, QWORD PTR [rdi+rdx*8+64]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+rcx*8+64]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+r8*8+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+48]
	sub rax, 8
	ror rax, 3
	shr rax, 27
	je 298f
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	mov eax, 0
	mov r14, 0
2100:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2100b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2101:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2102:
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
	jne 2102b
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
2103:
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
	jne 2103b
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
	jne 2101b
	mov ebp, 0
	mov r14, 0
2104:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2104b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2105:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2105b
	jmp 299f
298:
	cmp rcx, r8
	je 2106f
	mov r9, QWORD PTR [rdi+144]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	mov r14d, 0
2108:
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rax
	mov QWORD PTR [r8+r14*8+16], rax
	mov QWORD PTR [r8+r14*8+24], rax
	mov QWORD PTR [r8+r14*8+32], rax
	mov QWORD PTR [r8+r14*8+40], rax
	mov QWORD PTR [r8+r14*8+48], rax
	mov QWORD PTR [r8+r14*8+56], rax
	add r14, 8
	cmp r14, rcx
	jne 2108b
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2109:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+136]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+144]
	add rbp, rdx
	add rax, rdx
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	add rsi, 16
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
2110:
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	mov rdx, QWORD PTR [rdi+240]
	add rsi, 64
	xor eax, eax
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rdi+240], rax
	add rbp, 64
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 2110b
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 2111f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2113:
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	xor eax, eax
	adcx r8, rbp
	adcx r9, rcx
	adcx r10, rcx
	adcx r11, rcx
	adcx r12, rcx
	adcx r13, rcx
	adcx r14, rcx
	adcx r15, rcx
	mov ebp, 0
	adcx rbp, rax
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	add rsi, 64
	cmp rsi, rdx
	jne 2113b
	jmp 2112f
2111:
2112:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 2109b
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov eax, 0
	mov QWORD PTR [r9], rax
	mov QWORD PTR [r9+8], rax
	jmp 2107f
2106:
2107:
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
2114:
	mov rsi, rcx
	mov rbp, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+8], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+16], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+24], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+32], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+40], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+48], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+56], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov eax, 0
	mov QWORD PTR [rcx-8], rax
	add rbp, 64
	add rsi, 64
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, QWORD PTR [rdi+64]
	cmp rbp, rax
	jne 2115f
	jmp 2116f
2115:
2117:
	mov rdx, QWORD PTR [rcx-8]
	add rdx, -1
	adcx r8, QWORD PTR [rsi]
	adcx r9, QWORD PTR [rsi+8]
	adcx r10, QWORD PTR [rsi+16]
	adcx r11, QWORD PTR [rsi+24]
	adcx r12, QWORD PTR [rsi+32]
	adcx r13, QWORD PTR [rsi+40]
	adcx r14, QWORD PTR [rsi+48]
	adcx r15, QWORD PTR [rsi+56]
	mov eax, 0
	adcx rax, rax
	mov QWORD PTR [rcx-8], rax
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	add rbp, 64
	add rsi, 64
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, QWORD PTR [rdi+64]
	cmp rbp, rax
	jne 2117b
2116:
	mov rdx, QWORD PTR [rcx-8]
	add rdx, -1
	mov eax, 0
	mov rdx, QWORD PTR [rcx-16]
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov QWORD PTR [rcx+48], rax
	add rcx, 64
	cmp rcx, QWORD PTR [rdi+88]
	jne 2114b
	mov r8, rcx
	mov rbp, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rcx-16]
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+128]
	mov ebp, 0
	mov r14, 0
2118:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	mov rax, QWORD PTR [r8+r14*8+8]
	sbb rax, QWORD PTR [r10+r14*8+8]
	mov QWORD PTR [rsi+r14*8+8], rax
	mov rax, QWORD PTR [r8+r14*8+16]
	sbb rax, QWORD PTR [r10+r14*8+16]
	mov QWORD PTR [rsi+r14*8+16], rax
	mov rax, QWORD PTR [r8+r14*8+24]
	sbb rax, QWORD PTR [r10+r14*8+24]
	mov QWORD PTR [rsi+r14*8+24], rax
	mov rax, QWORD PTR [r8+r14*8+32]
	sbb rax, QWORD PTR [r10+r14*8+32]
	mov QWORD PTR [rsi+r14*8+32], rax
	mov rax, QWORD PTR [r8+r14*8+40]
	sbb rax, QWORD PTR [r10+r14*8+40]
	mov QWORD PTR [rsi+r14*8+40], rax
	mov rax, QWORD PTR [r8+r14*8+48]
	sbb rax, QWORD PTR [r10+r14*8+48]
	mov QWORD PTR [rsi+r14*8+48], rax
	mov rax, QWORD PTR [r8+r14*8+56]
	sbb rax, QWORD PTR [r10+r14*8+56]
	mov QWORD PTR [rsi+r14*8+56], rax
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 2118b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2119:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	cmovb rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	mov rax, QWORD PTR [rsi+r14*8+8]
	cmovb rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [rbx+r14*8+8], rax
	mov rax, QWORD PTR [rsi+r14*8+16]
	cmovb rax, QWORD PTR [r8+r14*8+16]
	mov QWORD PTR [rbx+r14*8+16], rax
	mov rax, QWORD PTR [rsi+r14*8+24]
	cmovb rax, QWORD PTR [r8+r14*8+24]
	mov QWORD PTR [rbx+r14*8+24], rax
	mov rax, QWORD PTR [rsi+r14*8+32]
	cmovb rax, QWORD PTR [r8+r14*8+32]
	mov QWORD PTR [rbx+r14*8+32], rax
	mov rax, QWORD PTR [rsi+r14*8+40]
	cmovb rax, QWORD PTR [r8+r14*8+40]
	mov QWORD PTR [rbx+r14*8+40], rax
	mov rax, QWORD PTR [rsi+r14*8+48]
	cmovb rax, QWORD PTR [r8+r14*8+48]
	mov QWORD PTR [rbx+r14*8+48], rax
	mov rax, QWORD PTR [rsi+r14*8+56]
	cmovb rax, QWORD PTR [r8+r14*8+56]
	mov QWORD PTR [rbx+r14*8+56], rax
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 2119b
299:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	movdqu XMMWORD PTR [rdi+128], xmm3
	movdqu XMMWORD PTR [rdi+144], xmm4
	movdqu XMMWORD PTR [rdi+160], xmm5
	movdqu XMMWORD PTR [rdi+224], xmm6
	movdqu XMMWORD PTR [rdi+240], xmm7
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
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
	add rbx, rax
	mov r14, 0
2120:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+64]
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
	add rsi, rax
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
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+64]
	mov rbp, QWORD PTR [r8]
	and rbp, -2
	mov r14, 1
2122:
	mov rax, QWORD PTR [r8+r14*8]
	cmp rbp, 1
	sbb rdx, rdx
	and rax, rdx
	or rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2122b
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
	mov rsi, QWORD PTR [rdi+64]
	mov r15, -1
	mov eax, 0
	sub rax, rbp
	and rax, rbp
	mov QWORD PTR [rbx+r12*8], rax
	mov rbp, QWORD PTR [rsi]
	mov r14, 1
2123:
	mov rax, QWORD PTR [rsi+r14*8]
	mov rdx, rax
	shl rdx, 63
	mov rcx, rbp
	shr rcx, 1
	or rcx, rdx
	xor rcx, rbp
	and rcx, r15
	xor rcx, rbp
	mov QWORD PTR [rbx+r14*8-8], rcx
	mov rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov rcx, rbp
	shr rcx, 1
	xor rcx, rbp
	and rcx, r15
	xor rcx, rbp
	mov QWORD PTR [rbx+r12*8-8], rcx
	mov rsi, rbx
	movabs r15, -2459565876494606883
	and r15, QWORD PTR [rbx+r12*8]
	cmp r15, 1
	sbb r15, r15
	xor r15, -1
	mov rbp, QWORD PTR [rsi]
	mov r14, 1
2124:
	mov rax, QWORD PTR [rsi+r14*8]
	mov rdx, rax
	shl rdx, 63
	mov rcx, rbp
	shr rcx, 1
	or rcx, rdx
	xor rcx, rbp
	and rcx, r15
	xor rcx, rbp
	mov QWORD PTR [rbx+r14*8-8], rcx
	mov rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2124b
	mov rcx, rbp
	shr rcx, 1
	xor rcx, rbp
	and rcx, r15
	xor rcx, rbp
	mov QWORD PTR [rbx+r12*8-8], rcx
	mov rsi, rbx
	movabs r15, -7378697629483820647
	and r15, QWORD PTR [rbx+r12*8]
	cmp r15, 1
	sbb r15, r15
	xor r15, -1
	mov rbp, QWORD PTR [rsi]
	mov r14, 1
2125:
	mov rax, QWORD PTR [rsi+r14*8]
	mov rdx, rax
	shl rdx, 63
	mov rcx, rbp
	shr rcx, 1
	or rcx, rdx
	xor rcx, rbp
	and rcx, r15
	xor rcx, rbp
	mov QWORD PTR [rbx+r14*8-8], rcx
	mov rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2125b
	mov rcx, rbp
	shr rcx, 1
	xor rcx, rbp
	and rcx, r15
	xor rcx, rbp
	mov QWORD PTR [rbx+r12*8-8], rcx
	mov rsi, rbx
	movabs r15, 1229782938247303441
	and r15, QWORD PTR [rbx+r12*8]
	cmp r15, 1
	sbb r15, r15
	xor r15, -1
	mov rbp, QWORD PTR [rsi]
	mov r14, 1
2126:
	mov rax, QWORD PTR [rsi+r14*8]
	mov rdx, rax
	shl rdx, 63
	mov rcx, rbp
	shr rcx, 1
	or rcx, rdx
	xor rcx, rbp
	and rcx, r15
	xor rcx, rbp
	mov QWORD PTR [rbx+r14*8-8], rcx
	mov rbp, rax
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov rcx, rbp
	shr rcx, 1
	xor rcx, rbp
	and rcx, r15
	xor rcx, rbp
	mov QWORD PTR [rbx+r12*8-8], rcx
	ret
	.p2align 6
