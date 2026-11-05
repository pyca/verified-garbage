// The functions of `src/internal/vg_p521_sqr_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_sqr_adx:
	xor r14d, r14d
	mov rdx, QWORD PTR [rbx]
	mulx r8, rbp, QWORD PTR [rbx+8]
	mov QWORD PTR [rdi+4032], rbp
	mulx r9, rax, QWORD PTR [rbx+16]
	adox r8, rax
	mov QWORD PTR [rdi+4040], r8
	mulx r10, rax, QWORD PTR [rbx+24]
	adox r9, rax
	mulx r11, rax, QWORD PTR [rbx+32]
	adox r10, rax
	mulx r12, rax, QWORD PTR [rbx+40]
	adox r11, rax
	mulx r13, rax, QWORD PTR [rbx+48]
	adox r12, rax
	mulx r15, rax, QWORD PTR [rbx+56]
	adox r13, rax
	adox r15, r14
	xor r14d, r14d
	mov rdx, QWORD PTR [rbx+8]
	mulx rcx, rax, QWORD PTR [rbx+16]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+4048], r9
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+4056], r10
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox r13, rax
	adcx r15, rcx
	mulx rbp, rax, QWORD PTR [rbx+56]
	adox r15, rax
	adcx rbp, r14
	mov rdx, QWORD PTR [rbx+40]
	mulx r8, rax, QWORD PTR [rbx+32]
	adox rbp, rax
	adcx r8, r14
	adox r8, r14
	xor r14d, r14d
	mov rdx, QWORD PTR [rbx+16]
	mulx rcx, rax, QWORD PTR [rbx+24]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+4064], r11
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+4072], r12
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r13, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox rbp, rax
	adcx r8, rcx
	mov rdx, QWORD PTR [rbx+48]
	mulx r9, rax, QWORD PTR [rbx+32]
	adox r8, rax
	adcx r9, r14
	mulx r10, rax, QWORD PTR [rbx+40]
	adox r9, rax
	adcx r10, r14
	adox r10, r14
	xor r14d, r14d
	mov rdx, QWORD PTR [rbx+24]
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r13, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+4080], r13
	mulx rcx, rax, QWORD PTR [rbx+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox r8, rax
	adcx r9, rcx
	mov rdx, QWORD PTR [rbx+56]
	mulx rcx, rax, QWORD PTR [rbx+32]
	adox r9, rax
	adcx r10, rcx
	mulx r11, rax, QWORD PTR [rbx+40]
	adox r10, rax
	adcx r11, r14
	mulx r12, rax, QWORD PTR [rbx+48]
	adox r11, rax
	adcx r12, r14
	adox r12, r14
	xor r14d, r14d
	mov rdx, QWORD PTR [rbx]
	mulx rcx, rax, rdx
	mov QWORD PTR [rdi+4024], rax
	mov rax, QWORD PTR [rdi+4032]
	adox rax, rax
	adcx rax, rcx
	mov QWORD PTR [rdi+4032], rax
	mov rax, QWORD PTR [rdi+4040]
	mov rdx, QWORD PTR [rbx+8]
	mulx rcx, rdx, rdx
	adox rax, rax
	adcx rax, rdx
	mov QWORD PTR [rdi+4040], rax
	mov rax, QWORD PTR [rdi+4048]
	adox rax, rax
	adcx rax, rcx
	mov QWORD PTR [rdi+4048], rax
	mov rax, QWORD PTR [rdi+4056]
	mov rdx, QWORD PTR [rbx+16]
	mulx rcx, rdx, rdx
	adox rax, rax
	adcx rax, rdx
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adox rax, rax
	adcx rax, rcx
	mov QWORD PTR [rdi+4064], rax
	mov rax, QWORD PTR [rdi+4072]
	mov rdx, QWORD PTR [rbx+24]
	mulx rcx, rdx, rdx
	adox rax, rax
	adcx rax, rdx
	mov QWORD PTR [rdi+4072], rax
	mov rax, QWORD PTR [rdi+4080]
	adox rax, rax
	adcx rax, rcx
	mov QWORD PTR [rdi+4080], rax
	mov rdx, QWORD PTR [rbx+32]
	mulx rcx, rdx, rdx
	adox r15, r15
	adcx r15, rdx
	adox rbp, rbp
	adcx rbp, rcx
	mov rdx, QWORD PTR [rbx+40]
	mulx rcx, rdx, rdx
	adox r8, r8
	adcx r8, rdx
	adox r9, r9
	adcx r9, rcx
	mov rdx, QWORD PTR [rbx+48]
	mulx rcx, rdx, rdx
	adox r10, r10
	adcx r10, rdx
	adox r11, r11
	adcx r11, rcx
	mov rdx, QWORD PTR [rbx+56]
	mulx r13, rdx, rdx
	adox r12, r12
	adcx r12, rdx
	adcx r13, r14
	adox r13, r14
	mov rdx, QWORD PTR [rbx+64]
	mov r14, rdx
	imul r14, r14
	add rdx, rdx
	mulx rcx, rax, QWORD PTR [rbx]
	adcx r15, rax
	adox rbp, rcx
	mulx rcx, rax, QWORD PTR [rbx+8]
	adcx rbp, rax
	adox r8, rcx
	mulx rcx, rax, QWORD PTR [rbx+16]
	adcx r8, rax
	adox r9, rcx
	mulx rcx, rax, QWORD PTR [rbx+24]
	adcx r9, rax
	adox r10, rcx
	mulx rcx, rax, QWORD PTR [rbx+32]
	adcx r10, rax
	adox r11, rcx
	mulx rcx, rax, QWORD PTR [rbx+40]
	adcx r11, rax
	adox r12, rcx
	mulx rcx, rax, QWORD PTR [rbx+48]
	adcx r12, rax
	adox r13, rcx
	mulx rcx, rax, QWORD PTR [rbx+56]
	adcx r13, rax
	adox r14, rcx
	adc r14, 0
	mov QWORD PTR [rdi+4088], r15
	mov rax, QWORD PTR [rdi+4024]
	mov rcx, rax
	shl rcx, 18
	or r14, rcx
	mov r15, rax
	shr r15, 46
	and r15d, 511
	mov rcx, QWORD PTR [rdi+4032]
	mov rdx, rcx
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4024], rcx
	mov rax, rdx
	mov rcx, QWORD PTR [rdi+4040]
	mov rdx, rcx
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4032], rcx
	mov rax, rdx
	mov rcx, QWORD PTR [rdi+4048]
	mov rdx, rcx
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4040], rcx
	mov rax, rdx
	mov rcx, QWORD PTR [rdi+4056]
	mov rdx, rcx
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4048], rcx
	mov rax, rdx
	mov rcx, QWORD PTR [rdi+4064]
	mov rdx, rcx
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4056], rcx
	mov rax, rdx
	mov rcx, QWORD PTR [rdi+4072]
	mov rdx, rcx
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4064], rcx
	mov rax, rdx
	mov rcx, QWORD PTR [rdi+4080]
	mov rdx, rcx
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4072], rcx
	mov rax, rdx
	mov rcx, QWORD PTR [rdi+4088]
	mov rdx, rcx
	shld rcx, rax, 9
	mov QWORD PTR [rdi+4080], rcx
	mov rax, rdx
	shr rax, 55
	xor edx, edx
	cmp rdx, -1
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
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
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
