// The functions of `src/internal/vg_p256_jac_add_tail_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_jac_add_tail_adx:
	mov rdx, QWORD PTR [rdi+896]
	or rdx, QWORD PTR [rdi+904]
	or rdx, QWORD PTR [rdi+912]
	or rdx, QWORD PTR [rdi+920]
	test rdx, rdx
	je 20f
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+904]
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+920]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+896]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+904]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+912]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+920]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+880]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+824]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+888]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+824]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, QWORD PTR [rdi+960]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+968]
	mulx r11, rax, QWORD PTR [rdi+976]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+984]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+968]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+984]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+976]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+984]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+960]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+968]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+976]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+984]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov QWORD PTR [rdi+632], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+608]
	sbb r9, QWORD PTR [rdi+616]
	sbb r10, QWORD PTR [rdi+624]
	sbb r11, QWORD PTR [rdi+632]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rdx, QWORD PTR [rdi+960]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+640]
	mulx r10, rax, QWORD PTR [rdi+648]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+656]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+664]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+968]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+664]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+976]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+664]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+984]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+664]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+640], r12
	mov QWORD PTR [rdi+648], r13
	mov QWORD PTR [rdi+656], r14
	mov QWORD PTR [rdi+664], r15
	mov rdx, QWORD PTR [rdi+928]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+952]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov QWORD PTR [rdi+952], r15
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+696]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	mov QWORD PTR [rdi+696], r15
	jmp 21f
20:
	mov rdx, QWORD PTR [rdi+960]
	or rdx, QWORD PTR [rdi+968]
	or rdx, QWORD PTR [rdi+976]
	or rdx, QWORD PTR [rdi+984]
	test rdx, rdx
	je 22f
	movabs rax, 0
	mov QWORD PTR [rdi+608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+632], rax
	movabs rax, 1
	mov QWORD PTR [rdi+640], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+648], rax
	movabs rax, -1
	mov QWORD PTR [rdi+656], rax
	movabs rax, 4294967294
	mov QWORD PTR [rdi+664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+696], rax
	jmp 23f
22:
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+552]
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+568]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+544]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+552]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+560]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+568]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+800]
	sbb r9, QWORD PTR [rdi+808]
	sbb r10, QWORD PTR [rdi+816]
	sbb r11, QWORD PTR [rdi+824]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12d, 0
	add r8, QWORD PTR [rdi+800]
	adc r9, QWORD PTR [rdi+808]
	adc r10, QWORD PTR [rdi+816]
	adc r11, QWORD PTR [rdi+824]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+608]
	mulx r10, rax, QWORD PTR [rdi+616]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+624]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+632]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+632]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+632]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+920]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+632]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, QWORD PTR [rdi+896]
	adc r9, QWORD PTR [rdi+904]
	adc r10, QWORD PTR [rdi+912]
	adc r11, QWORD PTR [rdi+920]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	mov QWORD PTR [rdi+696], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+904]
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+920]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+896]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+904]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+912]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+920]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov QWORD PTR [rdi+632], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+608]
	sbb r9, QWORD PTR [rdi+616]
	sbb r10, QWORD PTR [rdi+624]
	sbb r11, QWORD PTR [rdi+632]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+640]
	mulx r10, rax, QWORD PTR [rdi+648]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+656]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+664]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+664]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+664]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+920]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+664]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+640], r12
	mov QWORD PTR [rdi+648], r13
	mov QWORD PTR [rdi+656], r14
	mov QWORD PTR [rdi+664], r15
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+856]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
23:
21:
	ret
	.p2align 6
