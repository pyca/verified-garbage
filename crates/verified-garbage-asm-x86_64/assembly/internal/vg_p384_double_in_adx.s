// The functions of `src/internal/vg_p384_double_in_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_double_in_adx:
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+840]
	mulx r10, rax, QWORD PTR [rdi+848]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+856]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+864]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+872]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+872]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+872]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+872]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+872]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+864]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+872]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1168], r8
	mov QWORD PTR [rdi+1176], r9
	mov QWORD PTR [rdi+1184], r10
	mov QWORD PTR [rdi+1192], r11
	mov QWORD PTR [rdi+1200], r12
	mov QWORD PTR [rdi+1208], r13
	mov rdx, QWORD PTR [rdi+784]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+792]
	mulx r10, rax, QWORD PTR [rdi+800]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+808]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+816]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+824]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+792]
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
	mov rdx, QWORD PTR [rdi+800]
	xor ebp, ebp
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
	mov rdx, QWORD PTR [rdi+808]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+824]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+816]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+824]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+784]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+792]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+800]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+808]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+816]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+824]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	mov QWORD PTR [rdi+1288], r8
	mov QWORD PTR [rdi+1296], r9
	mov QWORD PTR [rdi+1304], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1264]
	adc r14, QWORD PTR [rdi+1272]
	adc r15, QWORD PTR [rdi+1280]
	adc r10, QWORD PTR [rdi+1288]
	adc r11, QWORD PTR [rdi+1296]
	adc r12, QWORD PTR [rdi+1304]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	mov QWORD PTR [rdi+1288], r10
	mov QWORD PTR [rdi+1296], r11
	mov QWORD PTR [rdi+1304], r12
	mov rdx, QWORD PTR [rdi+784]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+864]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+872]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+792]
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
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+800]
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
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+808]
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
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+816]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+824]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1168]
	mulx r10, rax, QWORD PTR [rdi+1176]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1184]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1192]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1200]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1208]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1224]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1248]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1256]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1216], r14
	mov QWORD PTR [rdi+1224], r15
	mov QWORD PTR [rdi+1232], r8
	mov QWORD PTR [rdi+1240], r9
	mov QWORD PTR [rdi+1248], r10
	mov QWORD PTR [rdi+1256], r11
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1216]
	adc r9, QWORD PTR [rdi+1224]
	adc r10, QWORD PTR [rdi+1232]
	adc r11, QWORD PTR [rdi+1240]
	adc r12, QWORD PTR [rdi+1248]
	adc r13, QWORD PTR [rdi+1256]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1168], r8
	mov QWORD PTR [rdi+1176], r9
	mov QWORD PTR [rdi+1184], r10
	mov QWORD PTR [rdi+1192], r11
	mov QWORD PTR [rdi+1200], r12
	mov QWORD PTR [rdi+1208], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1312]
	adc r9, QWORD PTR [rdi+1320]
	adc r10, QWORD PTR [rdi+1328]
	adc r11, QWORD PTR [rdi+1336]
	adc r12, QWORD PTR [rdi+1344]
	adc r13, QWORD PTR [rdi+1352]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1216]
	adc r9, QWORD PTR [rdi+1224]
	adc r10, QWORD PTR [rdi+1232]
	adc r11, QWORD PTR [rdi+1240]
	adc r12, QWORD PTR [rdi+1248]
	adc r13, QWORD PTR [rdi+1256]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1224]
	mulx r10, rax, QWORD PTR [rdi+1232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1248]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1256]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1224]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1256]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1248]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1216]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1224]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1232]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1240]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1248]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1256]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1264]
	mulx r10, rax, QWORD PTR [rdi+1272]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1280]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1288]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1296]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1304]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+760]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+768]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+776]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1312]
	adc r9, QWORD PTR [rdi+1320]
	adc r10, QWORD PTR [rdi+1328]
	adc r11, QWORD PTR [rdi+1336]
	adc r12, QWORD PTR [rdi+1344]
	adc r13, QWORD PTR [rdi+1352]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	sub r8, QWORD PTR [rdi+1312]
	sbb r9, QWORD PTR [rdi+1320]
	sbb r10, QWORD PTR [rdi+1328]
	sbb r11, QWORD PTR [rdi+1336]
	sbb r12, QWORD PTR [rdi+1344]
	sbb r13, QWORD PTR [rdi+1352]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1168], r8
	mov QWORD PTR [rdi+1176], r9
	mov QWORD PTR [rdi+1184], r10
	mov QWORD PTR [rdi+1192], r11
	mov QWORD PTR [rdi+1200], r12
	mov QWORD PTR [rdi+1208], r13
	mov rdx, QWORD PTR [rdi+1264]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1272]
	mulx r10, rax, QWORD PTR [rdi+1280]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1288]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1296]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1304]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1304]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1264]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1272]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1280]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1288]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1296]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1304]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	mov QWORD PTR [rdi+1288], r8
	mov QWORD PTR [rdi+1296], r9
	mov QWORD PTR [rdi+1304], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1264]
	adc r14, QWORD PTR [rdi+1272]
	adc r15, QWORD PTR [rdi+1280]
	adc r10, QWORD PTR [rdi+1288]
	adc r11, QWORD PTR [rdi+1296]
	adc r12, QWORD PTR [rdi+1304]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	mov QWORD PTR [rdi+1288], r10
	mov QWORD PTR [rdi+1296], r11
	mov QWORD PTR [rdi+1304], r12
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	sub r8, QWORD PTR [rdi+1312]
	sbb r9, QWORD PTR [rdi+1320]
	sbb r10, QWORD PTR [rdi+1328]
	sbb r11, QWORD PTR [rdi+1336]
	sbb r12, QWORD PTR [rdi+1344]
	sbb r13, QWORD PTR [rdi+1352]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1344]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1352]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1224]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1248]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1256]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+1264]
	sbb r9, QWORD PTR [rdi+1272]
	sbb r10, QWORD PTR [rdi+1280]
	sbb r11, QWORD PTR [rdi+1288]
	sbb r12, QWORD PTR [rdi+1296]
	sbb r13, QWORD PTR [rdi+1304]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	ret
	.p2align 6
