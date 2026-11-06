// The functions of `src/internal/vg_p521_mulw_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mulw_adx:
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rdi+4024], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rdi+4032], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rdi+4040], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rdi+4048], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rdi+4064], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rdi+4072], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rdi+4080], rax
	mov rax, QWORD PTR [rbx+64]
	mov QWORD PTR [rdi+4088], rax
	mov rbx, rcx
	mov rdx, QWORD PTR [rdi+4024]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbx]
	mov QWORD PTR [rdi+4024], rax
	mulx r9, rax, QWORD PTR [rbx+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rbx+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rbx+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rbx+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rbx+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rbx+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rbx+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rbx+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi+4032]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+4032], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rbx+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rbx+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi+4040]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+4040], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rbx+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rbx+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi+4048]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+4048], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rbx+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rbx+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi+4056]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+4056], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rbx+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rbx+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi+4064]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+4064], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rbx+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rbx+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi+4072]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+4072], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rbx+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rbx+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi+4080]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+4080], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rbx+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi+4088]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+4088], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rbx+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rbx+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	mov rcx, QWORD PTR [rdi+4024]
	shl rcx, 18
	or r14, rcx
	mov r15, QWORD PTR [rdi+4024]
	shr r15, 46
	and r15d, 511
	mov rax, QWORD PTR [rdi+4088]
	mov rcx, QWORD PTR [rdi+4080]
	shld rax, rcx, 9
	mov QWORD PTR [rdi+4080], rax
	mov rax, QWORD PTR [rdi+4072]
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4072], rcx
	mov rcx, QWORD PTR [rdi+4064]
	shld rax, rcx, 9
	mov QWORD PTR [rdi+4064], rax
	mov rax, QWORD PTR [rdi+4056]
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4056], rcx
	mov rcx, QWORD PTR [rdi+4048]
	shld rax, rcx, 9
	mov QWORD PTR [rdi+4048], rax
	mov rax, QWORD PTR [rdi+4040]
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4040], rcx
	mov rcx, QWORD PTR [rdi+4032]
	shld rax, rcx, 9
	mov QWORD PTR [rdi+4032], rax
	mov rax, QWORD PTR [rdi+4024]
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4024], rcx
	mov rax, QWORD PTR [rdi+4088]
	shr rax, 55
	xor edx, edx
	adc rbp, QWORD PTR [rdi+4024]
	adc r8, QWORD PTR [rdi+4032]
	adc r9, QWORD PTR [rdi+4040]
	adc r10, QWORD PTR [rdi+4048]
	adc r11, QWORD PTR [rdi+4056]
	adc r12, QWORD PTR [rdi+4064]
	adc r13, QWORD PTR [rdi+4072]
	adc r14, QWORD PTR [rdi+4080]
	adc r15, rax
	add rdi, rsi
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, rsi
	ret
	.p2align 6
