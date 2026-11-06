// The functions of `src/internal/vg_rsa_public_precomputed_checked_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precomputed_checked_adx:
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
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 222f
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
224:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 224b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
225:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
226:
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
	jne 226b
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
227:
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
	jne 227b
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
	jne 225b
	mov ebp, 0
	mov r14, 0
228:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 228b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
229:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 229b
	jmp 223f
222:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 230f
	mov r9, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
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
233:
	mov rax, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+80]
	add rdx, 16
	sub rax, rdx
	mov rdx, QWORD PTR [rax+r8*1]
	mov QWORD PTR [r8-16], rdx
	mulx rsi, rax, QWORD PTR [r9]
	add rax, QWORD PTR [r8]
	mov rdx, rax
	mulx rsi, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [r8-8], rdx
	mov ecx, 0
	mov ebp, 0
	mov r14d, 0
234:
	xor esi, esi
	mov rdx, QWORD PTR [r8-16]
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mulx rsi, r12, QWORD PTR [r9+r14*8+8]
	adcx r12, QWORD PTR [r8+r14*8+8]
	adox r12, rax
	mulx rax, r13, QWORD PTR [r9+r14*8+16]
	adcx r13, QWORD PTR [r8+r14*8+16]
	adox r13, rsi
	mulx rcx, r15, QWORD PTR [r9+r14*8+24]
	adcx r15, QWORD PTR [r8+r14*8+24]
	adox r15, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov rdx, QWORD PTR [r8-8]
	mulx rax, rsi, QWORD PTR [r10+r14*8]
	adcx r11, rsi
	adox r11, rbp
	mulx rbp, rsi, QWORD PTR [r10+r14*8+8]
	adcx r12, rsi
	adox r12, rax
	mulx rax, rsi, QWORD PTR [r10+r14*8+16]
	adcx r13, rsi
	adox r13, rbp
	mulx rbp, rsi, QWORD PTR [r10+r14*8+24]
	adcx r15, rsi
	adox r15, rax
	mov esi, 0
	adox rbp, rsi
	adcx rbp, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov QWORD PTR [r8+r14*8+16], r13
	mov QWORD PTR [r8+r14*8+24], r15
	add r14, 4
	cmp r14, rbx
	jne 234b
	mov rax, QWORD PTR [r8+r14*8]
	mov rsi, QWORD PTR [r8+r14*8+8]
	add rax, rcx
	adc rsi, 0
	add rax, rbp
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rsi
	add r8, 8
	mov rax, QWORD PTR [rdi+88]
	cmp r8, rax
	jne 233b
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+104]
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
	jmp 231f
230:
	mov r9, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	mov r14d, 0
237:
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
	jne 237b
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rax
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+8], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
238:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+72]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+96]
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
	cmp rax, QWORD PTR [rdi+48]
	jne 238b
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [r8]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [r8+8]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [r9]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [r9+8]
	mov QWORD PTR [rdi+248], rax
	mov eax, 0
	mov QWORD PTR [r9], rax
	mov QWORD PTR [r9+8], rax
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
243:
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
	jne 244f
	jmp 245f
244:
246:
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
	jne 246b
245:
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
	jne 243b
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
	mov rbx, QWORD PTR [rdi+104]
	mov ebp, 0
	mov r14, 0
247:
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
	jne 247b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
248:
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
	jne 248b
231:
223:
	mov r8, QWORD PTR [rdi+152]
	mov r9, QWORD PTR [rdi+160]
	mov r11d, 0
	mov r10d, 0
249:
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
	jne 249b
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
	je 250f
	mov eax, 0
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+216], rax
252:
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
253:
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	jne 254f
	jmp 255f
254:
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 256f
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
258:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
259:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
260:
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
	jne 260b
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
261:
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
	jne 261b
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
	jne 259b
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
	jmp 257f
256:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 264f
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
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
	mov ecx, 0
	mov r14d, 0
	mov rbx, rbp
	shr rbx, 4
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	cmp r14, rbx
	jne 268f
	jmp 269f
268:
270:
	xor esi, esi
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+8]
	adcx r11, QWORD PTR [r8+r14*8+8]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+8], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+16]
	adcx r11, QWORD PTR [r8+r14*8+16]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+16], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+24]
	adcx r11, QWORD PTR [r8+r14*8+24]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+24], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+32]
	adcx r11, QWORD PTR [r8+r14*8+32]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+32], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+40]
	adcx r11, QWORD PTR [r8+r14*8+40]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+40], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+48]
	adcx r11, QWORD PTR [r8+r14*8+48]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+48], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+56]
	adcx r11, QWORD PTR [r8+r14*8+56]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+56], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+64]
	adcx r11, QWORD PTR [r8+r14*8+64]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+64], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+72]
	adcx r11, QWORD PTR [r8+r14*8+72]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+72], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+80]
	adcx r11, QWORD PTR [r8+r14*8+80]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+80], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+88]
	adcx r11, QWORD PTR [r8+r14*8+88]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+88], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+96]
	adcx r11, QWORD PTR [r8+r14*8+96]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+96], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+104]
	adcx r11, QWORD PTR [r8+r14*8+104]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+104], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+112]
	adcx r11, QWORD PTR [r8+r14*8+112]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+112], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+120]
	adcx r11, QWORD PTR [r8+r14*8+120]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+120], r11
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	add r14, 16
	cmp r14, rbx
	jne 270b
269:
	mov rbx, rbp
	shr rbx, 2
	add rbx, rbx
	add rbx, rbx
	cmp r14, rbx
	jne 271f
	jmp 272f
271:
273:
	xor esi, esi
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mulx rsi, r12, QWORD PTR [r9+r14*8+8]
	adcx r12, QWORD PTR [r8+r14*8+8]
	adox r12, rax
	mulx rax, r13, QWORD PTR [r9+r14*8+16]
	adcx r13, QWORD PTR [r8+r14*8+16]
	adox r13, rsi
	mulx rcx, r15, QWORD PTR [r9+r14*8+24]
	adcx r15, QWORD PTR [r8+r14*8+24]
	adox r15, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov QWORD PTR [r8+r14*8+16], r13
	mov QWORD PTR [r8+r14*8+24], r15
	add r14, 4
	cmp r14, rbx
	jne 273b
272:
	mov rbx, rbp
	cmp r14, rbx
	jne 274f
	jmp 275f
274:
276:
	xor esi, esi
	mov rax, rcx
	mulx rcx, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov QWORD PTR [r8+r14*8], r11
	add r14, 1
	cmp r14, rbx
	jne 276b
275:
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 267b
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov r10, rbx
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
277:
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
	mov r15d, 0
	adcx r15, rsi
	adox r15, rsi
	add rbp, 4
	add r14, 8
	cmp rbp, r10
	jne 277b
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov r9, QWORD PTR [rdi+64]
	mov rbp, QWORD PTR [rdi+48]
	mov r10d, 0
278:
	mov rdx, QWORD PTR [r8]
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov rbx, rbp
	and rbx, 15
	cmp rbx, 0
	je 279f
	mov rbx, rbp
	shr rbx, 2
	add rbx, rbx
	add rbx, rbx
	mov ecx, 0
	mov r14d, 0
	cmp rbx, 0
	jne 281f
	jmp 282f
281:
283:
	xor esi, esi
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mulx rsi, r12, QWORD PTR [r9+r14*8+8]
	adcx r12, QWORD PTR [r8+r14*8+8]
	adox r12, rax
	mulx rax, r13, QWORD PTR [r9+r14*8+16]
	adcx r13, QWORD PTR [r8+r14*8+16]
	adox r13, rsi
	mulx rcx, r15, QWORD PTR [r9+r14*8+24]
	adcx r15, QWORD PTR [r8+r14*8+24]
	adox r15, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov QWORD PTR [r8+r14*8+16], r13
	mov QWORD PTR [r8+r14*8+24], r15
	add r14, 4
	cmp r14, rbx
	jne 283b
282:
	mov rbx, rbp
	cmp r14, rbx
	jne 284f
	jmp 285f
284:
286:
	xor esi, esi
	mov rax, rcx
	mulx rcx, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov QWORD PTR [r8+r14*8], r11
	add r14, 1
	cmp r14, rbx
	jne 286b
285:
	jmp 280f
279:
	mov rbx, rbp
	mov ecx, 0
	mov r14d, 0
287:
	xor esi, esi
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+8]
	adcx r11, QWORD PTR [r8+r14*8+8]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+8], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+16]
	adcx r11, QWORD PTR [r8+r14*8+16]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+16], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+24]
	adcx r11, QWORD PTR [r8+r14*8+24]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+24], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+32]
	adcx r11, QWORD PTR [r8+r14*8+32]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+32], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+40]
	adcx r11, QWORD PTR [r8+r14*8+40]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+40], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+48]
	adcx r11, QWORD PTR [r8+r14*8+48]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+48], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+56]
	adcx r11, QWORD PTR [r8+r14*8+56]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+56], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+64]
	adcx r11, QWORD PTR [r8+r14*8+64]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+64], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+72]
	adcx r11, QWORD PTR [r8+r14*8+72]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+72], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+80]
	adcx r11, QWORD PTR [r8+r14*8+80]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+80], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+88]
	adcx r11, QWORD PTR [r8+r14*8+88]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+88], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+96]
	adcx r11, QWORD PTR [r8+r14*8+96]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+96], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+104]
	adcx r11, QWORD PTR [r8+r14*8+104]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+104], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+112]
	adcx r11, QWORD PTR [r8+r14*8+112]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+112], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+120]
	adcx r11, QWORD PTR [r8+r14*8+120]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+120], r11
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	add r14, 16
	cmp r14, rbx
	jne 287b
280:
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	mov rax, QWORD PTR [rdi+88]
	cmp r8, rax
	jne 278b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
288:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 288b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
289:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 289b
	jmp 265f
264:
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+8], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
290:
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rbp, QWORD PTR [rdi+112]
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
	jne 290b
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 8
	je 291f
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 16
	je 293f
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+248], rax
295:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+112]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+112]
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
	je 296f
298:
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
	jne 298b
	jmp 297f
296:
297:
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
	je 299f
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+248], rax
	jmp 2100f
299:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 2101f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2103:
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
	jne 2103b
	jmp 2102f
2101:
2102:
2100:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 295b
	jmp 294f
293:
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2104:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+112]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+112]
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
2105:
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
	jne 2105b
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
	je 2106f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2108:
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
	jne 2108b
	jmp 2107f
2106:
2107:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 2104b
294:
	jmp 292f
291:
292:
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [r8]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [r8+8]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [r9]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [r9+8]
	mov QWORD PTR [rdi+248], rax
	mov eax, 0
	mov QWORD PTR [r9], rax
	mov QWORD PTR [r9+8], rax
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov r10, rbx
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2109:
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
	jne 2109b
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
2110:
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
	jne 2111f
	jmp 2112f
2111:
2113:
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
	jne 2113b
2112:
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
	jne 2110b
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
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2114:
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
	jne 2114b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2115:
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
	jne 2115b
265:
257:
255:
	mov rax, QWORD PTR [rdi+200]
	shr rax, 7
	and rax, 1
	jne 2116f
	jmp 2117f
2116:
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	jne 2118f
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2120:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
	mov eax, 1
	mov QWORD PTR [rdi+216], rax
	jmp 2119f
2118:
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 2121f
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
2123:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2124:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2125:
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
	jne 2125b
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
2126:
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
	jne 2126b
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
	jne 2124b
	mov ebp, 0
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
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2128:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2128b
	jmp 2122f
2121:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 2129f
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2131:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2131b
2132:
	mov rax, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+80]
	add rdx, 16
	sub rax, rdx
	mov rdx, QWORD PTR [rax+r8*1]
	mov QWORD PTR [r8-16], rdx
	mulx rsi, rax, QWORD PTR [r9]
	add rax, QWORD PTR [r8]
	mov rdx, rax
	mulx rsi, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [r8-8], rdx
	mov ecx, 0
	mov ebp, 0
	mov r14d, 0
2133:
	xor esi, esi
	mov rdx, QWORD PTR [r8-16]
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mulx rsi, r12, QWORD PTR [r9+r14*8+8]
	adcx r12, QWORD PTR [r8+r14*8+8]
	adox r12, rax
	mulx rax, r13, QWORD PTR [r9+r14*8+16]
	adcx r13, QWORD PTR [r8+r14*8+16]
	adox r13, rsi
	mulx rcx, r15, QWORD PTR [r9+r14*8+24]
	adcx r15, QWORD PTR [r8+r14*8+24]
	adox r15, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov rdx, QWORD PTR [r8-8]
	mulx rax, rsi, QWORD PTR [r10+r14*8]
	adcx r11, rsi
	adox r11, rbp
	mulx rbp, rsi, QWORD PTR [r10+r14*8+8]
	adcx r12, rsi
	adox r12, rax
	mulx rax, rsi, QWORD PTR [r10+r14*8+16]
	adcx r13, rsi
	adox r13, rbp
	mulx rbp, rsi, QWORD PTR [r10+r14*8+24]
	adcx r15, rsi
	adox r15, rax
	mov esi, 0
	adox rbp, rsi
	adcx rbp, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov QWORD PTR [r8+r14*8+16], r13
	mov QWORD PTR [r8+r14*8+24], r15
	add r14, 4
	cmp r14, rbx
	jne 2133b
	mov rax, QWORD PTR [r8+r14*8]
	mov rsi, QWORD PTR [r8+r14*8+8]
	add rax, rcx
	adc rsi, 0
	add rax, rbp
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rsi
	add r8, 8
	mov rax, QWORD PTR [rdi+88]
	cmp r8, rax
	jne 2132b
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+112]
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
	jmp 2130f
2129:
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	mov r14d, 0
2136:
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
	jne 2136b
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rax
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+8], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2137:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+112]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+104]
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
2138:
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
	jne 2138b
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
	je 2139f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2141:
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
	jne 2141b
	jmp 2140f
2139:
2140:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 2137b
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [r8]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [r8+8]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [r9]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [r9+8]
	mov QWORD PTR [rdi+248], rax
	mov eax, 0
	mov QWORD PTR [r9], rax
	mov QWORD PTR [r9+8], rax
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
2142:
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
	jne 2143f
	jmp 2144f
2143:
2145:
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
	jne 2145b
2144:
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
	jne 2142b
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
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2146:
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
	jne 2146b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2147:
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
	jne 2147b
2130:
2122:
2119:
2117:
	mov rax, QWORD PTR [rdi+200]
	add rax, rax
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+192]
	sub rax, 1
	mov QWORD PTR [rdi+192], rax
	jne 253b
	mov rax, QWORD PTR [rdi+184]
	add rax, 1
	mov QWORD PTR [rdi+184], rax
	cmp rax, QWORD PTR [rdi+160]
	jne 252b
	jmp 251f
250:
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2148:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov eax, 1
	mov QWORD PTR [rdi+216], rax
	mov eax, 16
	mov QWORD PTR [rdi+184], rax
2149:
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 2150f
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
2152:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2153:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2154:
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
	jne 2154b
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
2155:
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
	jne 2155b
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
	jne 2153b
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
	jmp 2151f
2150:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 2158f
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2160:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2160b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2161:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov ecx, 0
	mov r14d, 0
	mov rbx, rbp
	shr rbx, 4
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	add rbx, rbx
	cmp r14, rbx
	jne 2162f
	jmp 2163f
2162:
2164:
	xor esi, esi
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+8]
	adcx r11, QWORD PTR [r8+r14*8+8]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+8], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+16]
	adcx r11, QWORD PTR [r8+r14*8+16]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+16], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+24]
	adcx r11, QWORD PTR [r8+r14*8+24]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+24], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+32]
	adcx r11, QWORD PTR [r8+r14*8+32]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+32], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+40]
	adcx r11, QWORD PTR [r8+r14*8+40]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+40], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+48]
	adcx r11, QWORD PTR [r8+r14*8+48]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+48], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+56]
	adcx r11, QWORD PTR [r8+r14*8+56]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+56], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+64]
	adcx r11, QWORD PTR [r8+r14*8+64]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+64], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+72]
	adcx r11, QWORD PTR [r8+r14*8+72]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+72], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+80]
	adcx r11, QWORD PTR [r8+r14*8+80]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+80], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+88]
	adcx r11, QWORD PTR [r8+r14*8+88]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+88], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+96]
	adcx r11, QWORD PTR [r8+r14*8+96]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+96], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+104]
	adcx r11, QWORD PTR [r8+r14*8+104]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+104], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+112]
	adcx r11, QWORD PTR [r8+r14*8+112]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+112], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+120]
	adcx r11, QWORD PTR [r8+r14*8+120]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+120], r11
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	add r14, 16
	cmp r14, rbx
	jne 2164b
2163:
	mov rbx, rbp
	shr rbx, 2
	add rbx, rbx
	add rbx, rbx
	cmp r14, rbx
	jne 2165f
	jmp 2166f
2165:
2167:
	xor esi, esi
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mulx rsi, r12, QWORD PTR [r9+r14*8+8]
	adcx r12, QWORD PTR [r8+r14*8+8]
	adox r12, rax
	mulx rax, r13, QWORD PTR [r9+r14*8+16]
	adcx r13, QWORD PTR [r8+r14*8+16]
	adox r13, rsi
	mulx rcx, r15, QWORD PTR [r9+r14*8+24]
	adcx r15, QWORD PTR [r8+r14*8+24]
	adox r15, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov QWORD PTR [r8+r14*8+16], r13
	mov QWORD PTR [r8+r14*8+24], r15
	add r14, 4
	cmp r14, rbx
	jne 2167b
2166:
	mov rbx, rbp
	cmp r14, rbx
	jne 2168f
	jmp 2169f
2168:
2170:
	xor esi, esi
	mov rax, rcx
	mulx rcx, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov QWORD PTR [r8+r14*8], r11
	add r14, 1
	cmp r14, rbx
	jne 2170b
2169:
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2161b
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov r10, rbx
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2171:
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
	mov r15d, 0
	adcx r15, rsi
	adox r15, rsi
	add rbp, 4
	add r14, 8
	cmp rbp, r10
	jne 2171b
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov r9, QWORD PTR [rdi+64]
	mov rbp, QWORD PTR [rdi+48]
	mov r10d, 0
2172:
	mov rdx, QWORD PTR [r8]
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov rbx, rbp
	and rbx, 15
	cmp rbx, 0
	je 2173f
	mov rbx, rbp
	shr rbx, 2
	add rbx, rbx
	add rbx, rbx
	mov ecx, 0
	mov r14d, 0
	cmp rbx, 0
	jne 2175f
	jmp 2176f
2175:
2177:
	xor esi, esi
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mulx rsi, r12, QWORD PTR [r9+r14*8+8]
	adcx r12, QWORD PTR [r8+r14*8+8]
	adox r12, rax
	mulx rax, r13, QWORD PTR [r9+r14*8+16]
	adcx r13, QWORD PTR [r8+r14*8+16]
	adox r13, rsi
	mulx rcx, r15, QWORD PTR [r9+r14*8+24]
	adcx r15, QWORD PTR [r8+r14*8+24]
	adox r15, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov QWORD PTR [r8+r14*8+16], r13
	mov QWORD PTR [r8+r14*8+24], r15
	add r14, 4
	cmp r14, rbx
	jne 2177b
2176:
	mov rbx, rbp
	cmp r14, rbx
	jne 2178f
	jmp 2179f
2178:
2180:
	xor esi, esi
	mov rax, rcx
	mulx rcx, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov QWORD PTR [r8+r14*8], r11
	add r14, 1
	cmp r14, rbx
	jne 2180b
2179:
	jmp 2174f
2173:
	mov rbx, rbp
	mov ecx, 0
	mov r14d, 0
2181:
	xor esi, esi
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+8]
	adcx r11, QWORD PTR [r8+r14*8+8]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+8], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+16]
	adcx r11, QWORD PTR [r8+r14*8+16]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+16], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+24]
	adcx r11, QWORD PTR [r8+r14*8+24]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+24], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+32]
	adcx r11, QWORD PTR [r8+r14*8+32]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+32], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+40]
	adcx r11, QWORD PTR [r8+r14*8+40]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+40], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+48]
	adcx r11, QWORD PTR [r8+r14*8+48]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+48], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+56]
	adcx r11, QWORD PTR [r8+r14*8+56]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+56], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+64]
	adcx r11, QWORD PTR [r8+r14*8+64]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+64], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+72]
	adcx r11, QWORD PTR [r8+r14*8+72]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+72], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+80]
	adcx r11, QWORD PTR [r8+r14*8+80]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+80], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+88]
	adcx r11, QWORD PTR [r8+r14*8+88]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+88], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+96]
	adcx r11, QWORD PTR [r8+r14*8+96]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+96], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+104]
	adcx r11, QWORD PTR [r8+r14*8+104]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+104], r11
	mulx rax, r11, QWORD PTR [r9+r14*8+112]
	adcx r11, QWORD PTR [r8+r14*8+112]
	adox r11, rcx
	mov QWORD PTR [r8+r14*8+112], r11
	mulx rcx, r11, QWORD PTR [r9+r14*8+120]
	adcx r11, QWORD PTR [r8+r14*8+120]
	adox r11, rax
	mov QWORD PTR [r8+r14*8+120], r11
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	add r14, 16
	cmp r14, rbx
	jne 2181b
2174:
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	mov rax, QWORD PTR [rdi+88]
	cmp r8, rax
	jne 2172b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2182:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2182b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2183:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2183b
	jmp 2159f
2158:
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+8], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2184:
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rbp, QWORD PTR [rdi+112]
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
	jne 2184b
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 8
	je 2185f
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 16
	je 2187f
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+248], rax
2189:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+112]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+112]
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
	je 2190f
2192:
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
	jne 2192b
	jmp 2191f
2190:
2191:
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
	je 2193f
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+248], rax
	jmp 2194f
2193:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 2195f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2197:
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
	jne 2197b
	jmp 2196f
2195:
2196:
2194:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 2189b
	jmp 2188f
2187:
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2198:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+112]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+112]
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
2199:
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
	jne 2199b
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
	je 2200f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2202:
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
	jne 2202b
	jmp 2201f
2200:
2201:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 2198b
2188:
	jmp 2186f
2185:
2186:
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [r8]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [r8+8]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [r9]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [r9+8]
	mov QWORD PTR [rdi+248], rax
	mov eax, 0
	mov QWORD PTR [r9], rax
	mov QWORD PTR [r9+8], rax
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov r10, rbx
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2203:
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
	jne 2203b
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
2204:
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
	jne 2205f
	jmp 2206f
2205:
2207:
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
	jne 2207b
2206:
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
	jne 2204b
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
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2208:
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
	jne 2208b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2209:
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
	jne 2209b
2159:
2151:
	mov rax, QWORD PTR [rdi+184]
	sub rax, 1
	mov QWORD PTR [rdi+184], rax
	jne 2149b
251:
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 2210f
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
2212:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2212b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2213:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2214:
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
	jne 2214b
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
2215:
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
	jne 2215b
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
	jne 2213b
	mov ebp, 0
	mov r14, 0
2216:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2216b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2217:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2217b
	jmp 2211f
2210:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 2218f
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2220:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2220b
2221:
	mov rax, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+80]
	add rdx, 16
	sub rax, rdx
	mov rdx, QWORD PTR [rax+r8*1]
	mov QWORD PTR [r8-16], rdx
	mulx rsi, rax, QWORD PTR [r9]
	add rax, QWORD PTR [r8]
	mov rdx, rax
	mulx rsi, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [r8-8], rdx
	mov ecx, 0
	mov ebp, 0
	mov r14d, 0
2222:
	xor esi, esi
	mov rdx, QWORD PTR [r8-16]
	mulx rax, r11, QWORD PTR [r9+r14*8]
	adcx r11, QWORD PTR [r8+r14*8]
	adox r11, rcx
	mulx rsi, r12, QWORD PTR [r9+r14*8+8]
	adcx r12, QWORD PTR [r8+r14*8+8]
	adox r12, rax
	mulx rax, r13, QWORD PTR [r9+r14*8+16]
	adcx r13, QWORD PTR [r8+r14*8+16]
	adox r13, rsi
	mulx rcx, r15, QWORD PTR [r9+r14*8+24]
	adcx r15, QWORD PTR [r8+r14*8+24]
	adox r15, rax
	mov esi, 0
	adox rcx, rsi
	adcx rcx, rsi
	mov rdx, QWORD PTR [r8-8]
	mulx rax, rsi, QWORD PTR [r10+r14*8]
	adcx r11, rsi
	adox r11, rbp
	mulx rbp, rsi, QWORD PTR [r10+r14*8+8]
	adcx r12, rsi
	adox r12, rax
	mulx rax, rsi, QWORD PTR [r10+r14*8+16]
	adcx r13, rsi
	adox r13, rbp
	mulx rbp, rsi, QWORD PTR [r10+r14*8+24]
	adcx r15, rsi
	adox r15, rax
	mov esi, 0
	adox rbp, rsi
	adcx rbp, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov QWORD PTR [r8+r14*8+16], r13
	mov QWORD PTR [r8+r14*8+24], r15
	add r14, 4
	cmp r14, rbx
	jne 2222b
	mov rax, QWORD PTR [r8+r14*8]
	mov rsi, QWORD PTR [r8+r14*8+8]
	add rax, rcx
	adc rsi, 0
	add rax, rbp
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rsi
	add r8, 8
	mov rax, QWORD PTR [rdi+88]
	cmp r8, rax
	jne 2221b
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
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
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2224:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2224b
	jmp 2219f
2218:
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	mov r14d, 0
2225:
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
	jne 2225b
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rax
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+8], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2226:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+72]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+112]
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
2227:
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
	jne 2227b
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
	je 2228f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2230:
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
	jne 2230b
	jmp 2229f
2228:
2229:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 2226b
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov rax, QWORD PTR [r8]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [r8+8]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [r9]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [r9+8]
	mov QWORD PTR [rdi+248], rax
	mov eax, 0
	mov QWORD PTR [r9], rax
	mov QWORD PTR [r9+8], rax
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
2231:
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
	jne 2232f
	jmp 2233f
2232:
2234:
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
	jne 2234b
2233:
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
	jne 2231b
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
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2235:
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
	jne 2235b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2236:
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
	jne 2236b
2219:
2211:
	mov rbx, QWORD PTR [rdi+112]
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+176]
	mov rax, rcx
	and rax, 7
	cmp rax, 0
	je 2237f
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2239:
	mov rbp, rdx
	and rbp, 7
	je 2240f
	jmp 2241f
2240:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2241:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2239b
	jmp 2238f
2237:
	mov r14, rsi
	add r14, rcx
	mov edx, 0
2242:
	mov rax, QWORD PTR [rbx+rdx*1]
	and rax, r15
	bswap rax
	sub r14, 8
	mov QWORD PTR [r14], rax
	add rdx, 8
	cmp rdx, rcx
	jne 2242b
2238:
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
2243:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2243b
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
2244:
	mov BYTE PTR [r10], al
	add r10, 1
	sub r11, 1
	jne 2244b
22:
	ret
	.p2align 6
