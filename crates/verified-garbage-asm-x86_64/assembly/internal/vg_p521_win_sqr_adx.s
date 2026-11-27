// The functions of `src/internal/vg_p521_win_sqr_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_win_sqr_adx:
	xor eax, eax
	mov QWORD PTR [rdi+4024], rax
	mov rdx, QWORD PTR [rbx]
	mulx r9, r8, QWORD PTR [rbx+8]
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
	mov QWORD PTR [rdi+4032], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rbx+8]
	xor eax, eax
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
	mov QWORD PTR [rdi+4040], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rbx+16]
	xor eax, eax
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
	mov QWORD PTR [rdi+4048], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rbx+24]
	xor eax, eax
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
	mov QWORD PTR [rdi+4056], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rbx+32]
	xor eax, eax
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
	mov QWORD PTR [rdi+4064], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rbx+40]
	xor eax, eax
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
	mov QWORD PTR [rdi+4072], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rbx+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi+4080], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rbx+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rbx+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi+4088], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rbx]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4024]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4024], rdx
	mov rdx, QWORD PTR [rdi+4032]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4032], rdx
	mov rdx, QWORD PTR [rbx+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4040]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4040], rdx
	mov rdx, QWORD PTR [rdi+4048]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rbx+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rbx+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4072]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+4080]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rbx+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4088]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rbx+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rbx+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rbx+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rbx+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	mov edx, 512
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+4024]
	adox rax, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+4088], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+4032]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+4040]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+4048]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+4056]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+4064]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+4072]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+4080]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+4088]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	ret
	.p2align 6
