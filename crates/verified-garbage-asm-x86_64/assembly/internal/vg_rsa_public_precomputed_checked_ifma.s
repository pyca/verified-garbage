// The functions of `src/internal/vg_rsa_public_precomputed_checked_ifma.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precomputed_checked_ifma:
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
	mov r8, QWORD PTR [rdi+152]
	mov r9, QWORD PTR [rdi+160]
	mov r11d, 0
	mov r10d, 0
222:
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
	jne 222b
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
	je 223f
	mov eax, 0
	cmp rax, 1
	jmp 224f
223:
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 32
	je 225f
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 48
	je 227f
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 64
	jmp 228f
227:
	cmp r11, r11
228:
	jmp 226f
225:
	cmp r11, r11
226:
224:
	je 229f
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 231f
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
233:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 233b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
234:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
235:
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
	jne 235b
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
236:
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
	jne 236b
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
	jne 234b
	mov ebp, 0
	mov r14, 0
237:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 237b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
238:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 238b
	jmp 232f
231:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 239f
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
241:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 241b
242:
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
243:
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
	jne 243b
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
	jne 242b
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+104]
	mov ebp, 0
	mov r14, 0
244:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 244b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
245:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 245b
	jmp 240f
239:
	mov r9, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	mov r14d, 0
246:
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
	jne 246b
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
247:
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
248:
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
	jne 248b
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
	je 249f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
251:
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
	jne 251b
	jmp 250f
249:
250:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 247b
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
252:
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
	jne 253f
	jmp 254f
253:
255:
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
	jne 255b
254:
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
	jne 252b
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
256:
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
	jne 256b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
257:
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
	jne 257b
240:
232:
	mov r8, QWORD PTR [rdi+152]
	mov r9, QWORD PTR [rdi+160]
	mov r11d, 0
	mov r10d, 0
258:
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
	jne 258b
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
	je 259f
	mov eax, 0
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+216], rax
261:
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
262:
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	jne 263f
	jmp 264f
263:
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 265f
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
267:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
268:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
269:
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
	jne 269b
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
270:
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
	jne 270b
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
	jne 268b
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
	jmp 266f
265:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 273f
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
275:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 275b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
276:
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
	jne 277f
	jmp 278f
277:
279:
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
	jne 279b
278:
	mov rbx, rbp
	shr rbx, 2
	add rbx, rbx
	add rbx, rbx
	cmp r14, rbx
	jne 280f
	jmp 281f
280:
282:
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
	jne 282b
281:
	mov rbx, rbp
	cmp r14, rbx
	jne 283f
	jmp 284f
283:
285:
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
	jne 285b
284:
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 276b
	mov r9, QWORD PTR [rdi+112]
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
	mov r15d, 0
	adcx r15, rsi
	adox r15, rsi
	add rbp, 4
	add r14, 8
	cmp rbp, r10
	jne 286b
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov r9, QWORD PTR [rdi+64]
	mov rbp, QWORD PTR [rdi+48]
	mov r10d, 0
287:
	mov rdx, QWORD PTR [r8]
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov rbx, rbp
	and rbx, 15
	cmp rbx, 0
	je 288f
	mov rbx, rbp
	shr rbx, 2
	add rbx, rbx
	add rbx, rbx
	mov ecx, 0
	mov r14d, 0
	cmp rbx, 0
	jne 290f
	jmp 291f
290:
292:
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
	jne 292b
291:
	mov rbx, rbp
	cmp r14, rbx
	jne 293f
	jmp 294f
293:
295:
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
	jne 295b
294:
	jmp 289f
288:
	mov rbx, rbp
	mov ecx, 0
	mov r14d, 0
296:
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
	jne 296b
289:
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
	jne 287b
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
297:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 297b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
298:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 298b
	jmp 274f
273:
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
299:
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
	jne 299b
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 8
	je 2100f
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 16
	je 2102f
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+248], rax
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
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 2105f
2107:
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
	jne 2107b
	jmp 2106f
2105:
2106:
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
	je 2108f
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+248], rax
	jmp 2109f
2108:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 2110f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2112:
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
	jne 2112b
	jmp 2111f
2110:
2111:
2109:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 2104b
	jmp 2103f
2102:
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2113:
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
2114:
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
	jne 2114b
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
	je 2115f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2117:
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
	jne 2117b
	jmp 2116f
2115:
2116:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 2113b
2103:
	jmp 2101f
2100:
2101:
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
2118:
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
	jne 2118b
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
2119:
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
	jne 2120f
	jmp 2121f
2120:
2122:
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
	jne 2122b
2121:
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
	jne 2119b
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
2123:
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
	jne 2123b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2124:
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
	jne 2124b
274:
266:
264:
	mov rax, QWORD PTR [rdi+200]
	shr rax, 7
	and rax, 1
	jne 2125f
	jmp 2126f
2125:
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	jne 2127f
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2129:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov eax, 1
	mov QWORD PTR [rdi+216], rax
	jmp 2128f
2127:
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 2130f
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
2132:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2132b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2133:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2134:
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
	jne 2134b
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
2135:
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
	jne 2135b
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
	jne 2133b
	mov ebp, 0
	mov r14, 0
2136:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2136b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2137:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2137b
	jmp 2131f
2130:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 2138f
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
2140:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2140b
2141:
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
2142:
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
	jne 2142b
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
	jne 2141b
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2143:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2143b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2144:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	jmp 2139f
2138:
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	mov r14d, 0
2145:
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
	jne 2145b
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
2146:
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
2147:
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
	jne 2147b
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
	je 2148f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2150:
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
	jne 2150b
	jmp 2149f
2148:
2149:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 2146b
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
2151:
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
	jne 2152f
	jmp 2153f
2152:
2154:
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
	jne 2154b
2153:
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
	jne 2151b
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
2155:
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
	jne 2155b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2156:
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
	jne 2156b
2139:
2131:
2128:
2126:
	mov rax, QWORD PTR [rdi+200]
	add rax, rax
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+192]
	sub rax, 1
	mov QWORD PTR [rdi+192], rax
	jne 262b
	mov rax, QWORD PTR [rdi+184]
	add rax, 1
	mov QWORD PTR [rdi+184], rax
	cmp rax, QWORD PTR [rdi+160]
	jne 261b
	jmp 260f
259:
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+112]
	mov r14, 0
2157:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2157b
	mov eax, 1
	mov QWORD PTR [rdi+216], rax
	mov eax, 16
	mov QWORD PTR [rdi+184], rax
2158:
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 2159f
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
2161:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2161b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2162:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2163:
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
	jne 2163b
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
2164:
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
	jne 2164b
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
	jne 2162b
	mov ebp, 0
	mov r14, 0
2165:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2165b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2166:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2166b
	jmp 2160f
2159:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 2167f
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
2169:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2169b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2170:
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
	jne 2171f
	jmp 2172f
2171:
2173:
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
	jne 2173b
2172:
	mov rbx, rbp
	shr rbx, 2
	add rbx, rbx
	add rbx, rbx
	cmp r14, rbx
	jne 2174f
	jmp 2175f
2174:
2176:
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
	jne 2176b
2175:
	mov rbx, rbp
	cmp r14, rbx
	jne 2177f
	jmp 2178f
2177:
2179:
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
	jne 2179b
2178:
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2170b
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov r10, rbx
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2180:
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
	jne 2180b
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov r9, QWORD PTR [rdi+64]
	mov rbp, QWORD PTR [rdi+48]
	mov r10d, 0
2181:
	mov rdx, QWORD PTR [r8]
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov rbx, rbp
	and rbx, 15
	cmp rbx, 0
	je 2182f
	mov rbx, rbp
	shr rbx, 2
	add rbx, rbx
	add rbx, rbx
	mov ecx, 0
	mov r14d, 0
	cmp rbx, 0
	jne 2184f
	jmp 2185f
2184:
2186:
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
	jne 2186b
2185:
	mov rbx, rbp
	cmp r14, rbx
	jne 2187f
	jmp 2188f
2187:
2189:
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
	jne 2189b
2188:
	jmp 2183f
2182:
	mov rbx, rbp
	mov ecx, 0
	mov r14d, 0
2190:
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
	jne 2190b
2183:
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
	jne 2181b
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
	jmp 2168f
2167:
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
2193:
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
	jne 2193b
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 8
	je 2194f
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 16
	je 2196f
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+248], rax
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
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 2199f
2201:
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
	jne 2201b
	jmp 2200f
2199:
2200:
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
	je 2202f
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+248], rax
	jmp 2203f
2202:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 2204f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2206:
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
	jne 2206b
	jmp 2205f
2204:
2205:
2203:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 2198b
	jmp 2197f
2196:
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
2207:
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
2208:
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
	jne 2208b
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
	je 2209f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2211:
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
	jne 2211b
	jmp 2210f
2209:
2210:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+48]
	sub rcx, 8
	cmp rax, rcx
	jne 2207b
2197:
	jmp 2195f
2194:
2195:
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
2212:
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
	jne 2212b
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
2213:
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
	jne 2214f
	jmp 2215f
2214:
2216:
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
	jne 2216b
2215:
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
	jne 2213b
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
2217:
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
	jne 2217b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2218:
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
	jne 2218b
2168:
2160:
	mov rax, QWORD PTR [rdi+184]
	sub rax, 1
	mov QWORD PTR [rdi+184], rax
	jne 2158b
260:
	mov rax, QWORD PTR [rdi+48]
	sub rax, 4
	ror rax, 2
	shr rax, 28
	je 2219f
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
2221:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2221b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2222:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2223:
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
	jne 2223b
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
2224:
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
	jne 2224b
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
	jne 2222b
	mov ebp, 0
	mov r14, 0
2225:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2225b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2226:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2226b
	jmp 2220f
2219:
	mov rax, QWORD PTR [rdi+48]
	and rax, 7
	cmp rax, 0
	je 2227f
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
2229:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2229b
2230:
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
2231:
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
	jne 2231b
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
	jne 2230b
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2232:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2232b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2233:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2233b
	jmp 2228f
2227:
	mov r9, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	mov r14d, 0
2234:
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
	jne 2234b
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
2235:
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
2236:
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
	jne 2236b
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
	je 2237f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
2239:
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
	jne 2239b
	jmp 2238f
2237:
2238:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 2235b
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
2240:
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
	jne 2241f
	jmp 2242f
2241:
2243:
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
	jne 2243b
2242:
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
	jne 2240b
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
2244:
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
	jne 2244b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2245:
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
	jne 2245b
2228:
2220:
	jmp 230f
229:
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 32
	je 2246f
	mov rax, QWORD PTR [rdi+48]
	cmp rax, 48
	je 2248f
	mov rbx, rdi
	add rbx, 1312
	movabs r12, 4503599627370495
	mov rsi, rdi
	add rsi, 256
	mov r11, rbx
	add r11, 0
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
	mov QWORD PTR [r11+320], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+448], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+480], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+512], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+544], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+576], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+608], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+360], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+392], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+456], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+488], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+520], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+552], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+584], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+256]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+616], rax
	mov rax, QWORD PTR [rsi+256]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+264]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+264]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+272]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+280]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+280]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+288]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+288]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+296]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+304]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+304]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+312]
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+312]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+320]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+320]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+328]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [rsi+328]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+336]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	mov rax, QWORD PTR [rsi+336]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+344]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+400], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+432], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+352]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+464], rax
	mov rax, QWORD PTR [rsi+352]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+360]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+496], rax
	mov rax, QWORD PTR [rsi+360]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+368]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+528], rax
	mov rax, QWORD PTR [rsi+368]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+376]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+560], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+592], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+384]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+624], rax
	mov rax, QWORD PTR [rsi+384]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+392]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+392]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+400]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+400]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+408]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+408]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+416]
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+416]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+424]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+424]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+432]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+432]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+440]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+440]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+448]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+448]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+312], rax
	mov rax, QWORD PTR [rsi+448]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+456]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [rsi+456]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+464]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	mov rax, QWORD PTR [rsi+464]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+472]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	mov rax, QWORD PTR [rsi+472]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+480]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+440], rax
	mov rax, QWORD PTR [rsi+480]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+472], rax
	mov rax, QWORD PTR [rsi+480]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+488]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+504], rax
	mov rax, QWORD PTR [rsi+488]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+496]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+536], rax
	mov rax, QWORD PTR [rsi+496]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+504]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+568], rax
	mov rax, QWORD PTR [rsi+504]
	shr rax, 24
	and rax, r12
	mov QWORD PTR [r11+600], rax
	mov eax, 0
	mov QWORD PTR [r11+632], rax
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [rbx+640], rax
	mov QWORD PTR [rbx+648], rax
	mov QWORD PTR [rbx+656], rax
	mov QWORD PTR [rbx+664], rax
	mov rsi, rdi
	add rsi, 2368
	mov r11, rbx
	add r11, 1584
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
	mov QWORD PTR [r11+320], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+448], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+480], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+512], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+544], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+576], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+608], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+360], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+392], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+456], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+488], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+520], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+552], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+584], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+256]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+616], rax
	mov rax, QWORD PTR [rsi+256]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+264]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+264]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+272]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+280]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+280]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+288]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+288]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+296]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+304]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+304]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+312]
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+312]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+320]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+320]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+328]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [rsi+328]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+336]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	mov rax, QWORD PTR [rsi+336]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+344]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+400], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+432], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+352]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+464], rax
	mov rax, QWORD PTR [rsi+352]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+360]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+496], rax
	mov rax, QWORD PTR [rsi+360]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+368]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+528], rax
	mov rax, QWORD PTR [rsi+368]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+376]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+560], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+592], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+384]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+624], rax
	mov rax, QWORD PTR [rsi+384]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+392]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+392]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+400]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+400]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+408]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+408]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+416]
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+416]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+424]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+424]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+432]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+432]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+440]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+440]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+448]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+448]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+312], rax
	mov rax, QWORD PTR [rsi+448]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+456]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [rsi+456]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+464]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	mov rax, QWORD PTR [rsi+464]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+472]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	mov rax, QWORD PTR [rsi+472]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+480]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+440], rax
	mov rax, QWORD PTR [rsi+480]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+472], rax
	mov rax, QWORD PTR [rsi+480]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+488]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+504], rax
	mov rax, QWORD PTR [rsi+488]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+496]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+536], rax
	mov rax, QWORD PTR [rsi+496]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+504]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+568], rax
	mov rax, QWORD PTR [rsi+504]
	shr rax, 24
	and rax, r12
	mov QWORD PTR [r11+600], rax
	mov eax, 0
	mov QWORD PTR [r11+632], rax
	mov r13d, 0
2250:
	cmp r13, 1
	je 2251f
	cmp r13, 2
	je 2253f
	cmp r13, 19
	je 2255f
	mov r8, rbx
	add r8, 1584
	mov r9, rbx
	add r9, 1584
	mov r11, rbx
	add r11, 1584
	jmp 2256f
2255:
	mov r8, rbx
	add r8, 1584
	mov r9, rbx
	add r9, 2224
	mov r11, rbx
	add r11, 1584
2256:
	jmp 2254f
2253:
	mov rsi, rdi
	add rsi, 784
	mov r11, rbx
	add r11, 2224
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
	mov QWORD PTR [r11+320], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+448], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+480], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+512], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+544], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+576], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+608], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+360], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+392], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+456], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+488], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+520], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+552], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+584], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+256]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+616], rax
	mov rax, QWORD PTR [rsi+256]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+264]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+264]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+272]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+280]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+280]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+288]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+288]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+296]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+304]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+304]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+312]
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+312]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+320]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+320]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+328]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [rsi+328]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+336]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	mov rax, QWORD PTR [rsi+336]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+344]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+400], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+432], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+352]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+464], rax
	mov rax, QWORD PTR [rsi+352]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+360]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+496], rax
	mov rax, QWORD PTR [rsi+360]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+368]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+528], rax
	mov rax, QWORD PTR [rsi+368]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+376]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+560], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+592], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+384]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+624], rax
	mov rax, QWORD PTR [rsi+384]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+392]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+392]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+400]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+400]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+408]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+408]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+416]
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+416]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+424]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+424]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+432]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+432]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+440]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+440]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+448]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+448]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+312], rax
	mov rax, QWORD PTR [rsi+448]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+456]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [rsi+456]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+464]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	mov rax, QWORD PTR [rsi+464]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+472]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	mov rax, QWORD PTR [rsi+472]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+480]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+440], rax
	mov rax, QWORD PTR [rsi+480]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+472], rax
	mov rax, QWORD PTR [rsi+480]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+488]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+504], rax
	mov rax, QWORD PTR [rsi+488]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+496]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+536], rax
	mov rax, QWORD PTR [rsi+496]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+504]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+568], rax
	mov rax, QWORD PTR [rsi+504]
	shr rax, 24
	and rax, r12
	mov QWORD PTR [r11+600], rax
	mov eax, 0
	mov QWORD PTR [r11+632], rax
	mov r8, rbx
	add r8, 2224
	mov r9, rbx
	add r9, 1584
	mov r11, rbx
	add r11, 1584
2254:
	jmp 2252f
2251:
	mov r11, rbx
	mov eax, 0
	mov QWORD PTR [r11+2224], rax
	mov QWORD PTR [r11+2256], rax
	mov QWORD PTR [r11+2288], rax
	mov QWORD PTR [r11+2320], rax
	mov QWORD PTR [r11+2352], rax
	mov QWORD PTR [r11+2384], rax
	mov QWORD PTR [r11+2416], rax
	mov QWORD PTR [r11+2448], rax
	mov QWORD PTR [r11+2480], rax
	mov QWORD PTR [r11+2512], rax
	mov QWORD PTR [r11+2544], rax
	mov QWORD PTR [r11+2576], rax
	mov QWORD PTR [r11+2608], rax
	mov QWORD PTR [r11+2640], rax
	mov QWORD PTR [r11+2672], rax
	mov QWORD PTR [r11+2704], rax
	mov QWORD PTR [r11+2736], rax
	mov QWORD PTR [r11+2768], rax
	mov QWORD PTR [r11+2800], rax
	mov QWORD PTR [r11+2832], rax
	mov QWORD PTR [r11+2232], rax
	mov QWORD PTR [r11+2264], rax
	mov QWORD PTR [r11+2296], rax
	mov QWORD PTR [r11+2328], rax
	mov QWORD PTR [r11+2360], rax
	mov QWORD PTR [r11+2392], rax
	mov QWORD PTR [r11+2424], rax
	mov QWORD PTR [r11+2456], rax
	mov QWORD PTR [r11+2488], rax
	mov QWORD PTR [r11+2520], rax
	mov QWORD PTR [r11+2552], rax
	mov QWORD PTR [r11+2584], rax
	mov QWORD PTR [r11+2616], rax
	mov QWORD PTR [r11+2648], rax
	mov QWORD PTR [r11+2680], rax
	mov QWORD PTR [r11+2712], rax
	mov QWORD PTR [r11+2744], rax
	mov QWORD PTR [r11+2776], rax
	mov QWORD PTR [r11+2808], rax
	mov QWORD PTR [r11+2840], rax
	mov QWORD PTR [r11+2240], rax
	mov QWORD PTR [r11+2272], rax
	mov QWORD PTR [r11+2304], rax
	mov QWORD PTR [r11+2336], rax
	mov QWORD PTR [r11+2368], rax
	mov QWORD PTR [r11+2400], rax
	mov QWORD PTR [r11+2432], rax
	mov QWORD PTR [r11+2464], rax
	mov QWORD PTR [r11+2496], rax
	mov QWORD PTR [r11+2528], rax
	mov QWORD PTR [r11+2560], rax
	mov QWORD PTR [r11+2592], rax
	mov QWORD PTR [r11+2624], rax
	mov QWORD PTR [r11+2656], rax
	mov QWORD PTR [r11+2688], rax
	mov QWORD PTR [r11+2720], rax
	mov QWORD PTR [r11+2752], rax
	mov QWORD PTR [r11+2784], rax
	mov QWORD PTR [r11+2816], rax
	mov QWORD PTR [r11+2848], rax
	mov QWORD PTR [r11+2248], rax
	mov QWORD PTR [r11+2280], rax
	mov QWORD PTR [r11+2312], rax
	mov QWORD PTR [r11+2344], rax
	mov QWORD PTR [r11+2376], rax
	mov QWORD PTR [r11+2408], rax
	mov QWORD PTR [r11+2440], rax
	mov QWORD PTR [r11+2472], rax
	mov QWORD PTR [r11+2504], rax
	mov QWORD PTR [r11+2536], rax
	mov QWORD PTR [r11+2568], rax
	mov QWORD PTR [r11+2600], rax
	mov QWORD PTR [r11+2632], rax
	mov QWORD PTR [r11+2664], rax
	mov QWORD PTR [r11+2696], rax
	mov QWORD PTR [r11+2728], rax
	mov QWORD PTR [r11+2760], rax
	mov QWORD PTR [r11+2792], rax
	mov QWORD PTR [r11+2824], rax
	mov QWORD PTR [r11+2856], rax
	movabs rax, 281474976710656
	mov QWORD PTR [r11+2352], rax
	mov r8, rbx
	add r8, 1584
	mov r9, rbx
	add r9, 2224
	mov r11, rbx
	add r11, 1584
2252:
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
2257:
	mov rax, QWORD PTR [r9]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm0, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm0, 52
	vmovq xmm23, xmm23
	vpaddq ymm1, ymm1, ymm23
	valignq ymm0, ymm22, ymm0, 1
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm1, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm1, 52
	vmovq xmm23, xmm23
	vpaddq ymm2, ymm2, ymm23
	valignq ymm1, ymm22, ymm1, 1
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm2, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm2, 52
	vmovq xmm23, xmm23
	vpaddq ymm3, ymm3, ymm23
	valignq ymm2, ymm22, ymm2, 1
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm3, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm3, 52
	vmovq xmm23, xmm23
	vpaddq ymm4, ymm4, ymm23
	valignq ymm3, ymm22, ymm3, 1
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm4, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm4, 52
	vmovq xmm23, xmm23
	vpaddq ymm5, ymm5, ymm23
	valignq ymm4, ymm22, ymm4, 1
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm5, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm5, 52
	vmovq xmm23, xmm23
	vpaddq ymm6, ymm6, ymm23
	valignq ymm5, ymm22, ymm5, 1
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm6, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm6, 52
	vmovq xmm23, xmm23
	vpaddq ymm7, ymm7, ymm23
	valignq ymm6, ymm22, ymm6, 1
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm7, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm7, 52
	vmovq xmm23, xmm23
	vpaddq ymm8, ymm8, ymm23
	valignq ymm7, ymm22, ymm7, 1
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm8, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm8, 52
	vmovq xmm23, xmm23
	vpaddq ymm9, ymm9, ymm23
	valignq ymm8, ymm22, ymm8, 1
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm9, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm9, 52
	vmovq xmm23, xmm23
	vpaddq ymm10, ymm10, ymm23
	valignq ymm9, ymm22, ymm9, 1
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+320]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm10, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm10, 52
	vmovq xmm23, xmm23
	vpaddq ymm11, ymm11, ymm23
	valignq ymm10, ymm22, ymm10, 1
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+352]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm11, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm11, 52
	vmovq xmm23, xmm23
	vpaddq ymm12, ymm12, ymm23
	valignq ymm11, ymm22, ymm11, 1
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+384]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm12, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm12, 52
	vmovq xmm23, xmm23
	vpaddq ymm13, ymm13, ymm23
	valignq ymm12, ymm22, ymm12, 1
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+416]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm13, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm13, 52
	vmovq xmm23, xmm23
	vpaddq ymm14, ymm14, ymm23
	valignq ymm13, ymm22, ymm13, 1
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+448]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm14, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm14, 52
	vmovq xmm23, xmm23
	vpaddq ymm15, ymm15, ymm23
	valignq ymm14, ymm22, ymm14, 1
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+480]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm15, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm15, 52
	vmovq xmm23, xmm23
	vpaddq ymm16, ymm16, ymm23
	valignq ymm15, ymm22, ymm15, 1
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+512]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm16, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm16, 52
	vmovq xmm23, xmm23
	vpaddq ymm17, ymm17, ymm23
	valignq ymm16, ymm22, ymm16, 1
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+544]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm17, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm17, 52
	vmovq xmm23, xmm23
	vpaddq ymm18, ymm18, ymm23
	valignq ymm17, ymm22, ymm17, 1
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+576]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm18, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm18, 52
	vmovq xmm23, xmm23
	vpaddq ymm19, ymm19, ymm23
	valignq ymm18, ymm22, ymm18, 1
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+608]
	mov rax, QWORD PTR [r9+608]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	vpmadd52luq ymm19, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpxorq ymm23, ymm23, ymm23
	vpmadd52luq ymm23, ymm19, YMMWORD PTR [r10+640]
	vpbroadcastq ymm21, xmm23
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm21, YMMWORD PTR [r10+32]
	vpsrlq ymm23, ymm19, 52
	vmovq xmm23, xmm23
	vpaddq ymm0, ymm0, ymm23
	valignq ymm19, ymm22, ymm19, 1
	vpmadd52huq ymm0, ymm21, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm21, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm21, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm21, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm21, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm21, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm21, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm21, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm21, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm21, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm21, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm21, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm21, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm21, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm21, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm21, YMMWORD PTR [r10+256]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+320]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52luq ymm9, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm9, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm10, ymm20, YMMWORD PTR [r8+352]
	vpmadd52huq ymm10, ymm20, YMMWORD PTR [r8+320]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r10+352]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r10+320]
	vpmadd52luq ymm11, ymm20, YMMWORD PTR [r8+384]
	vpmadd52huq ymm11, ymm20, YMMWORD PTR [r8+352]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r10+384]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+352]
	vpmadd52luq ymm12, ymm20, YMMWORD PTR [r8+416]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r8+384]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+416]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+384]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r8+448]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r8+416]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+448]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r10+416]
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r8+480]
	vpmadd52huq ymm14, ymm20, YMMWORD PTR [r8+448]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r10+480]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r10+448]
	vpmadd52luq ymm15, ymm20, YMMWORD PTR [r8+512]
	vpmadd52huq ymm15, ymm20, YMMWORD PTR [r8+480]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r10+512]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r10+480]
	vpmadd52luq ymm16, ymm20, YMMWORD PTR [r8+544]
	vpmadd52huq ymm16, ymm20, YMMWORD PTR [r8+512]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r10+544]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r10+512]
	vpmadd52luq ymm17, ymm20, YMMWORD PTR [r8+576]
	vpmadd52huq ymm17, ymm20, YMMWORD PTR [r8+544]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+544]
	vpmadd52luq ymm18, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm18, ymm20, YMMWORD PTR [r8+576]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+608]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r10+576]
	vpmadd52huq ymm19, ymm20, YMMWORD PTR [r8+608]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r10+608]
	add r9, 8
	sub rcx, 1
	jne 2257b
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
	vmovdqu64 YMMWORD PTR [r11+320], ymm10
	vmovdqu64 YMMWORD PTR [r11+352], ymm11
	vmovdqu64 YMMWORD PTR [r11+384], ymm12
	vmovdqu64 YMMWORD PTR [r11+416], ymm13
	vmovdqu64 YMMWORD PTR [r11+448], ymm14
	vmovdqu64 YMMWORD PTR [r11+480], ymm15
	vmovdqu64 YMMWORD PTR [r11+512], ymm16
	vmovdqu64 YMMWORD PTR [r11+544], ymm17
	vmovdqu64 YMMWORD PTR [r11+576], ymm18
	vmovdqu64 YMMWORD PTR [r11+608], ymm19
	movabs r12, 4503599627370495
	mov edx, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+256]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+288]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+320]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+320], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+352]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+384]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+416]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+448]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+448], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+480]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+480], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+512]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+512], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+544]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+544], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+576]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+576], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+608]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+608], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+264]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+296]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+328]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+360]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+360], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+392]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+392], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+424]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+456]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+456], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+488]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+488], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+520]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+520], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+552]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+552], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+584]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+584], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+616]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+616], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+272]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+304]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+336]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+368]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+400]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+400], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+432]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+432], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+464]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+464], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+496]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+496], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+528]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+528], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+560]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+560], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+592]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+592], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+624]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+624], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+280]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+312]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+344]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+376]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+408]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+440]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+440], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+472]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+472], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+504]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+504], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+536]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+536], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+568]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+568], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+600]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+600], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+632]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+632], rax
	shr rdx, 52
	add r13, 1
	cmp r13, 20
	jne 2250b
	vzeroupper
	mov r11, rbx
	add r11, 1584
	mov r8, rbx
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
	mov rcx, QWORD PTR [r11+320]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+352]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+352]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+384]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+384]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+416]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+416]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+448]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+448]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+480]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+512]
	or rax, rcx
	mov rcx, QWORD PTR [r11+544]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+544]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+576]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+576]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+608]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+608]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+8]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+168]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+200]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+232]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+264]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+264]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+296]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+296]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+328]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+328]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+360]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+200], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+392]
	or rax, rcx
	mov rcx, QWORD PTR [r11+424]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+208], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+424]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+456]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+216], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+456]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+488]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+224], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+488]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+520]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+232], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+520]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+552]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+584]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+240], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+584]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+616]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+248], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+616]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+256], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+264], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+272], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+280], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+288], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+176]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+296], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+208]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+304], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+272]
	or rax, rcx
	mov rcx, QWORD PTR [r11+304]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+312], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+304]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+336]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+320], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+336]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+368]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+328], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+368]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+400]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+336], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+400]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+432]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+464]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+344], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+464]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+496]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+352], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+496]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+528]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+360], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+528]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+560]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+368], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+560]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+592]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+624]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+376], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+624]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+384], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+392], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+400], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+88]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+408], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+416], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+424], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+216]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+248]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+432], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+248]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+280]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+440], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+280]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+312]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+344]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+448], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+344]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+376]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+456], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+376]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+408]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+464], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+408]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+440]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+472], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+440]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+472]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+504]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+480], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+504]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+536]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+488], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+536]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+568]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+496], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+568]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+600]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+504], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+600]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+632]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+512], rax
	mov rbx, rdi
	add rbx, 3424
	mov r10, rdi
	add r10, 256
	mov r12d, 64
	mov rsi, rdi
	add rsi, 1840
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
	jmp 2249f
2248:
	mov rbx, rdi
	add rbx, 1056
	movabs r12, 4503599627370495
	mov rsi, rdi
	add rsi, 256
	mov r11, rbx
	add r11, 0
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
	mov QWORD PTR [r11+320], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+448], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+360], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+392], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+456], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+256]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+256]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+264]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [rsi+264]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+272]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+400], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+280]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+432], rax
	mov rax, QWORD PTR [rsi+280]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+288]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+464], rax
	mov rax, QWORD PTR [rsi+288]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+296]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+304]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+304]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+312]
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+312]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+320]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+320]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+328]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+328]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+336]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+336]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+344]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+352]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	mov rax, QWORD PTR [rsi+352]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+360]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [rsi+360]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+368]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	mov rax, QWORD PTR [rsi+368]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+376]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+440], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 60
	and rax, r12
	mov QWORD PTR [r11+472], rax
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [rbx+480], rax
	mov QWORD PTR [rbx+488], rax
	mov QWORD PTR [rbx+496], rax
	mov QWORD PTR [rbx+504], rax
	mov rsi, rdi
	add rsi, 1856
	mov r11, rbx
	add r11, 1200
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
	mov QWORD PTR [r11+320], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+448], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+360], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+392], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+456], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+256]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+256]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+264]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [rsi+264]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+272]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+400], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+280]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+432], rax
	mov rax, QWORD PTR [rsi+280]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+288]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+464], rax
	mov rax, QWORD PTR [rsi+288]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+296]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+304]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+304]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+312]
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+312]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+320]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+320]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+328]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+328]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+336]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+336]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+344]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+352]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	mov rax, QWORD PTR [rsi+352]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+360]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [rsi+360]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+368]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	mov rax, QWORD PTR [rsi+368]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+376]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+440], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 60
	and rax, r12
	mov QWORD PTR [r11+472], rax
	mov r13d, 0
2260:
	cmp r13, 1
	je 2261f
	cmp r13, 2
	je 2263f
	cmp r13, 19
	je 2265f
	mov r8, rbx
	add r8, 1200
	mov r9, rbx
	add r9, 1200
	mov r11, rbx
	add r11, 1200
	jmp 2266f
2265:
	mov r8, rbx
	add r8, 1200
	mov r9, rbx
	add r9, 1680
	mov r11, rbx
	add r11, 1200
2266:
	jmp 2264f
2263:
	mov rsi, rdi
	add rsi, 656
	mov r11, rbx
	add r11, 1680
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
	mov QWORD PTR [r11+320], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+448], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+360], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+392], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+456], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+256]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+256]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+264]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [rsi+264]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+272]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+400], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+280]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+432], rax
	mov rax, QWORD PTR [rsi+280]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+288]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+464], rax
	mov rax, QWORD PTR [rsi+288]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+296]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+304]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+304]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+312]
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+312]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+320]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+320]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+328]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+328]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+336]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+336]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+344]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+352]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	mov rax, QWORD PTR [rsi+352]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+360]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [rsi+360]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+368]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	mov rax, QWORD PTR [rsi+368]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+376]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+440], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 60
	and rax, r12
	mov QWORD PTR [r11+472], rax
	mov r8, rbx
	add r8, 1680
	mov r9, rbx
	add r9, 1200
	mov r11, rbx
	add r11, 1200
2264:
	jmp 2262f
2261:
	mov r11, rbx
	mov eax, 0
	mov QWORD PTR [r11+1680], rax
	mov QWORD PTR [r11+1712], rax
	mov QWORD PTR [r11+1744], rax
	mov QWORD PTR [r11+1776], rax
	mov QWORD PTR [r11+1808], rax
	mov QWORD PTR [r11+1840], rax
	mov QWORD PTR [r11+1872], rax
	mov QWORD PTR [r11+1904], rax
	mov QWORD PTR [r11+1936], rax
	mov QWORD PTR [r11+1968], rax
	mov QWORD PTR [r11+2000], rax
	mov QWORD PTR [r11+2032], rax
	mov QWORD PTR [r11+2064], rax
	mov QWORD PTR [r11+2096], rax
	mov QWORD PTR [r11+2128], rax
	mov QWORD PTR [r11+1688], rax
	mov QWORD PTR [r11+1720], rax
	mov QWORD PTR [r11+1752], rax
	mov QWORD PTR [r11+1784], rax
	mov QWORD PTR [r11+1816], rax
	mov QWORD PTR [r11+1848], rax
	mov QWORD PTR [r11+1880], rax
	mov QWORD PTR [r11+1912], rax
	mov QWORD PTR [r11+1944], rax
	mov QWORD PTR [r11+1976], rax
	mov QWORD PTR [r11+2008], rax
	mov QWORD PTR [r11+2040], rax
	mov QWORD PTR [r11+2072], rax
	mov QWORD PTR [r11+2104], rax
	mov QWORD PTR [r11+2136], rax
	mov QWORD PTR [r11+1696], rax
	mov QWORD PTR [r11+1728], rax
	mov QWORD PTR [r11+1760], rax
	mov QWORD PTR [r11+1792], rax
	mov QWORD PTR [r11+1824], rax
	mov QWORD PTR [r11+1856], rax
	mov QWORD PTR [r11+1888], rax
	mov QWORD PTR [r11+1920], rax
	mov QWORD PTR [r11+1952], rax
	mov QWORD PTR [r11+1984], rax
	mov QWORD PTR [r11+2016], rax
	mov QWORD PTR [r11+2048], rax
	mov QWORD PTR [r11+2080], rax
	mov QWORD PTR [r11+2112], rax
	mov QWORD PTR [r11+2144], rax
	mov QWORD PTR [r11+1704], rax
	mov QWORD PTR [r11+1736], rax
	mov QWORD PTR [r11+1768], rax
	mov QWORD PTR [r11+1800], rax
	mov QWORD PTR [r11+1832], rax
	mov QWORD PTR [r11+1864], rax
	mov QWORD PTR [r11+1896], rax
	mov QWORD PTR [r11+1928], rax
	mov QWORD PTR [r11+1960], rax
	mov QWORD PTR [r11+1992], rax
	mov QWORD PTR [r11+2024], rax
	mov QWORD PTR [r11+2056], rax
	mov QWORD PTR [r11+2088], rax
	mov QWORD PTR [r11+2120], rax
	mov QWORD PTR [r11+2152], rax
	movabs rax, 68719476736
	mov QWORD PTR [r11+1776], rax
	mov r8, rbx
	add r8, 1200
	mov r9, rbx
	add r9, 1680
	mov r11, rbx
	add r11, 1200
2262:
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
2267:
	mov rax, QWORD PTR [r9]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm0, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm0, 52
	vmovq xmm18, xmm18
	vpaddq ymm1, ymm1, ymm18
	valignq ymm0, ymm17, ymm0, 1
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm1, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm1, 52
	vmovq xmm18, xmm18
	vpaddq ymm2, ymm2, ymm18
	valignq ymm1, ymm17, ymm1, 1
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm2, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm2, 52
	vmovq xmm18, xmm18
	vpaddq ymm3, ymm3, ymm18
	valignq ymm2, ymm17, ymm2, 1
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm3, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm3, 52
	vmovq xmm18, xmm18
	vpaddq ymm4, ymm4, ymm18
	valignq ymm3, ymm17, ymm3, 1
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm4, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm4, 52
	vmovq xmm18, xmm18
	vpaddq ymm5, ymm5, ymm18
	valignq ymm4, ymm17, ymm4, 1
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm5, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm5, 52
	vmovq xmm18, xmm18
	vpaddq ymm6, ymm6, ymm18
	valignq ymm5, ymm17, ymm5, 1
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm6, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm6, 52
	vmovq xmm18, xmm18
	vpaddq ymm7, ymm7, ymm18
	valignq ymm6, ymm17, ymm6, 1
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm7, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm7, 52
	vmovq xmm18, xmm18
	vpaddq ymm8, ymm8, ymm18
	valignq ymm7, ymm17, ymm7, 1
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm8, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm8, 52
	vmovq xmm18, xmm18
	vpaddq ymm9, ymm9, ymm18
	valignq ymm8, ymm17, ymm8, 1
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm9, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm9, 52
	vmovq xmm18, xmm18
	vpaddq ymm10, ymm10, ymm18
	valignq ymm9, ymm17, ymm9, 1
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+320]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm10, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm10, 52
	vmovq xmm18, xmm18
	vpaddq ymm11, ymm11, ymm18
	valignq ymm10, ymm17, ymm10, 1
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+352]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm11, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm11, 52
	vmovq xmm18, xmm18
	vpaddq ymm12, ymm12, ymm18
	valignq ymm11, ymm17, ymm11, 1
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+384]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm12, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm12, 52
	vmovq xmm18, xmm18
	vpaddq ymm13, ymm13, ymm18
	valignq ymm12, ymm17, ymm12, 1
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+416]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm13, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm13, 52
	vmovq xmm18, xmm18
	vpaddq ymm14, ymm14, ymm18
	valignq ymm13, ymm17, ymm13, 1
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+448]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm14, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm14, 52
	vmovq xmm18, xmm18
	vpaddq ymm0, ymm0, ymm18
	valignq ymm14, ymm17, ymm14, 1
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+448]
	add r9, 8
	sub rcx, 1
	jne 2267b
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
	vmovdqu64 YMMWORD PTR [r11+320], ymm10
	vmovdqu64 YMMWORD PTR [r11+352], ymm11
	vmovdqu64 YMMWORD PTR [r11+384], ymm12
	vmovdqu64 YMMWORD PTR [r11+416], ymm13
	vmovdqu64 YMMWORD PTR [r11+448], ymm14
	movabs r12, 4503599627370495
	mov edx, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+256]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+288]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+320]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+320], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+352]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+384]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+416]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+448]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+448], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+264]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+296]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+328]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+360]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+360], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+392]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+392], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+424]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+456]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+456], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+272]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+304]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+336]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+368]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+400]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+400], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+432]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+432], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+464]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+464], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+280]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+312]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+344]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+376]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+408]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+440]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+440], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+472]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+472], rax
	shr rdx, 52
	add r13, 1
	cmp r13, 20
	jne 2260b
	vzeroupper
	mov r11, rbx
	add r11, 1200
	mov r8, rbx
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
	mov rcx, QWORD PTR [r11+320]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+352]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+352]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+384]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+384]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+416]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+416]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+448]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+448]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+168]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+200]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+232]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+264]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+264]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+296]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+296]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+328]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+328]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+360]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+392]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+392]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+424]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+424]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+456]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+456]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+200], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+208], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+216], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+224], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+176]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+232], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+208]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+272]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+240], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+272]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+304]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+248], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+304]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+336]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+256], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+336]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+368]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+264], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+368]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+400]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+432]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+272], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+432]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+464]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+280], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+464]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+288], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+296], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+304], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+312], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+320], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+328], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+216]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+248]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+336], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+248]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+280]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+312]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+344], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+312]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+344]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+352], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+344]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+376]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+360], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+376]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+408]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+368], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+408]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+440]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+472]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+376], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+472]
	shr rcx, 4
	or rax, rcx
	mov QWORD PTR [r8+384], rax
	mov rbx, rdi
	add rbx, 2656
	mov r10, rdi
	add r10, 256
	mov r12d, 48
	mov rsi, rdi
	add rsi, 1456
	mov ebp, 0
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
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2269:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2269b
2249:
	jmp 2247f
2246:
	mov rbx, rdi
	add rbx, 800
	movabs r12, 4503599627370495
	mov rsi, rdi
	add rsi, 256
	mov r11, rbx
	add r11, 0
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
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [rbx+320], rax
	mov QWORD PTR [rbx+328], rax
	mov QWORD PTR [rbx+336], rax
	mov QWORD PTR [rbx+344], rax
	mov rsi, rdi
	add rsi, 1344
	mov r11, rbx
	add r11, 816
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
	mov r13d, 0
2270:
	cmp r13, 1
	je 2271f
	cmp r13, 2
	je 2273f
	cmp r13, 19
	je 2275f
	mov r8, rbx
	add r8, 816
	mov r9, rbx
	add r9, 816
	mov r11, rbx
	add r11, 816
	jmp 2276f
2275:
	mov r8, rbx
	add r8, 816
	mov r9, rbx
	add r9, 1136
	mov r11, rbx
	add r11, 816
2276:
	jmp 2274f
2273:
	mov rsi, rdi
	add rsi, 528
	mov r11, rbx
	add r11, 1136
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
	mov r8, rbx
	add r8, 1136
	mov r9, rbx
	add r9, 816
	mov r11, rbx
	add r11, 816
2274:
	jmp 2272f
2271:
	mov r11, rbx
	mov eax, 0
	mov QWORD PTR [r11+1136], rax
	mov QWORD PTR [r11+1168], rax
	mov QWORD PTR [r11+1200], rax
	mov QWORD PTR [r11+1232], rax
	mov QWORD PTR [r11+1264], rax
	mov QWORD PTR [r11+1296], rax
	mov QWORD PTR [r11+1328], rax
	mov QWORD PTR [r11+1360], rax
	mov QWORD PTR [r11+1392], rax
	mov QWORD PTR [r11+1424], rax
	mov QWORD PTR [r11+1144], rax
	mov QWORD PTR [r11+1176], rax
	mov QWORD PTR [r11+1208], rax
	mov QWORD PTR [r11+1240], rax
	mov QWORD PTR [r11+1272], rax
	mov QWORD PTR [r11+1304], rax
	mov QWORD PTR [r11+1336], rax
	mov QWORD PTR [r11+1368], rax
	mov QWORD PTR [r11+1400], rax
	mov QWORD PTR [r11+1432], rax
	mov QWORD PTR [r11+1152], rax
	mov QWORD PTR [r11+1184], rax
	mov QWORD PTR [r11+1216], rax
	mov QWORD PTR [r11+1248], rax
	mov QWORD PTR [r11+1280], rax
	mov QWORD PTR [r11+1312], rax
	mov QWORD PTR [r11+1344], rax
	mov QWORD PTR [r11+1376], rax
	mov QWORD PTR [r11+1408], rax
	mov QWORD PTR [r11+1440], rax
	mov QWORD PTR [r11+1160], rax
	mov QWORD PTR [r11+1192], rax
	mov QWORD PTR [r11+1224], rax
	mov QWORD PTR [r11+1256], rax
	mov QWORD PTR [r11+1288], rax
	mov QWORD PTR [r11+1320], rax
	mov QWORD PTR [r11+1352], rax
	mov QWORD PTR [r11+1384], rax
	mov QWORD PTR [r11+1416], rax
	mov QWORD PTR [r11+1448], rax
	movabs rax, 16777216
	mov QWORD PTR [r11+1200], rax
	mov r8, rbx
	add r8, 816
	mov r9, rbx
	add r9, 1136
	mov r11, rbx
	add r11, 816
2272:
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
	vpxorq ymm18, ymm18, ymm18
	mov rax, QWORD PTR [r9]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8]
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
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
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
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
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
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
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
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
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
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
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
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
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+8]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm9, ymm18, ymm9, 1
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
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+40]
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
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
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
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+72]
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
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+104]
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
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+136]
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
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+168]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+200]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+232]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+264]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+296]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
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
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
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
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm9, ymm18, ymm9, 1
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
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
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
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
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
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
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
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
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
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
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
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+176]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+208]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+240]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+272]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+304]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
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
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+24]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm9, ymm18, ymm9, 1
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
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+56]
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
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
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
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+88]
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
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+120]
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
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+152]
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
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+184]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+216]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+248]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+280]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+312]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
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
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	valignq ymm9, ymm18, ymm9, 1
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
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
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
	movabs r12, 4503599627370495
	mov edx, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+256]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+288]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+264]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+296]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+272]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+304]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+280]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+312]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	shr rdx, 52
	add r13, 1
	cmp r13, 20
	jne 2270b
	vzeroupper
	mov r11, rbx
	add r11, 816
	mov r8, rbx
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
	mov rbx, rdi
	add rbx, 1888
	mov r10, rdi
	add r10, 256
	mov r12d, 32
	mov rsi, rdi
	add rsi, 1072
	mov ebp, 0
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
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2278:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2278b
2247:
230:
	mov rbx, QWORD PTR [rdi+112]
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+176]
	mov rax, rcx
	and rax, 7
	cmp rax, 0
	je 2279f
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2281:
	mov rbp, rdx
	and rbp, 7
	je 2282f
	jmp 2283f
2282:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2283:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2281b
	jmp 2280f
2279:
	mov r14, rsi
	add r14, rcx
	mov edx, 0
2284:
	mov rax, QWORD PTR [rbx+rdx*1]
	and rax, r15
	bswap rax
	sub r14, 8
	mov QWORD PTR [r14], rax
	add rdx, 8
	cmp rdx, rcx
	jne 2284b
2280:
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
2285:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2285b
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
2286:
	mov BYTE PTR [r10], al
	add r10, 1
	sub r11, 1
	jne 2286b
22:
	ret
	.p2align 6
