// The functions of `src/internal/vg_p384_mul_mod_n_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul_mod_n_adx:
	mov esi, esi
	mov edx, edx
	mov ecx, ecx
	movq xmm0, rbx
	movq xmm1, rbp
	movq xmm2, r12
	movq xmm3, r13
	movq xmm4, r14
	movq xmm5, r15
	mov rbx, rdx
	add rbx, rdi
	add rcx, rdi
	cmp rbx, rcx
	movq xmm6, rsi
	mov rsi, rcx
	mov rax, QWORD PTR [rdi+4000]
	movq xmm7, rax
	mov rax, QWORD PTR [rdi+4008]
	movq xmm8, rax
	mov rax, QWORD PTR [rdi+4016]
	movq xmm9, rax
	mov rax, QWORD PTR [rdi+4024]
	movq xmm10, rax
	mov rax, QWORD PTR [rdi+4032]
	movq xmm11, rax
	mov rax, QWORD PTR [rdi+4040]
	movq xmm12, rax
	movabs rax, -1374695839762142861
	mov QWORD PTR [rdi+4000], rax
	movabs rax, 6348401684107011962
	mov QWORD PTR [rdi+4008], rax
	movabs rax, -4079331616924160545
	mov QWORD PTR [rdi+4016], rax
	movabs rax, -1
	mov QWORD PTR [rdi+4024], rax
	movabs rax, -1
	mov QWORD PTR [rdi+4032], rax
	movabs rax, -1
	mov QWORD PTR [rdi+4040], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rdx, QWORD PTR [rbx]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rsi]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, rcx
	adox r14, rbp
	adcx r15, rbp
	adox r15, rbp
	mov rax, r8
	movabs rcx, 7986114184663260229
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+4000]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+4008]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+4016]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+4024]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+4032]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+4040]
	adox r13, rax
	adcx r14, rcx
	adox r14, rbp
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rbx+8]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rsi]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rsi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rsi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rsi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rsi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rsi+40]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rax, r9
	movabs rcx, 7986114184663260229
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+4000]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+4008]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+4016]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+4024]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+4032]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+4040]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rbx+16]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rsi]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rsi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rsi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rsi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rsi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rsi+40]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rax, r10
	movabs rcx, 7986114184663260229
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+4000]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+4008]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+4016]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+4024]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+4032]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+4040]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rdx, QWORD PTR [rbx+24]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rsi]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rsi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rsi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rsi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rsi+32]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rsi+40]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r11
	movabs rcx, 7986114184663260229
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+4000]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+4008]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+4016]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+4024]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+4032]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+4040]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rdx, QWORD PTR [rbx+32]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rsi]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rsi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rsi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rsi+24]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rsi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rsi+40]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	mov rax, r12
	movabs rcx, 7986114184663260229
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+4000]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+4008]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+4016]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+4024]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+4032]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+4040]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	mov rdx, QWORD PTR [rbx+40]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rsi]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rsi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rsi+16]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rsi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rsi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rsi+40]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	mov rax, r13
	movabs rcx, 7986114184663260229
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+4000]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+4008]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+4016]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+4024]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+4032]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+4040]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	mov rax, r14
	sub rax, QWORD PTR [rdi+4000]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+4008]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+4016]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+4024]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+4032]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+4040]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	movq rsi, xmm6
	add rsi, rdi
	mov QWORD PTR [rsi], r14
	mov QWORD PTR [rsi+8], r15
	mov QWORD PTR [rsi+16], r8
	mov QWORD PTR [rsi+24], r9
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	movq rax, xmm7
	mov QWORD PTR [rdi+4000], rax
	movq rax, xmm8
	mov QWORD PTR [rdi+4008], rax
	movq rax, xmm9
	mov QWORD PTR [rdi+4016], rax
	movq rax, xmm10
	mov QWORD PTR [rdi+4024], rax
	movq rax, xmm11
	mov QWORD PTR [rdi+4032], rax
	movq rax, xmm12
	mov QWORD PTR [rdi+4040], rax
	movq rbx, xmm0
	movq rbp, xmm1
	movq r12, xmm2
	movq r13, xmm3
	movq r14, xmm4
	movq r15, xmm5
	ret
	.p2align 6
