// The functions of `src/internal/vg_p384_check_point_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_check_point_adx:
	movq xmm0, rbx
	movq xmm1, rbp
	movq xmm2, r12
	movq xmm3, r13
	movq xmm4, r14
	movq xmm5, r15
	mov rdx, QWORD PTR [rdi+1648]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+1656]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+1664]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+1672]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+1680]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1688]
	sbb rdx, QWORD PTR [rdi+104]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1792]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+1800]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+1808]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+1816]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+1824]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1832]
	sbb rdx, QWORD PTR [rdi+104]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1648]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1936]
	mulx r10, rax, QWORD PTR [rdi+1944]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1952]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1960]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1968]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1656]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1664]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1672]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1688]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov QWORD PTR [rdi+1696], r14
	mov QWORD PTR [rdi+1704], r15
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov rdx, QWORD PTR [rdi+1792]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1936]
	mulx r10, rax, QWORD PTR [rdi+1944]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1952]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1960]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1968]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1800]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1808]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1816]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1824]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov rdx, QWORD PTR [rdi+1832]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1936]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1944]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1952]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1960]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1968]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1976]
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
	mov QWORD PTR [rdi+1744], r14
	mov QWORD PTR [rdi+1752], r15
	mov QWORD PTR [rdi+1760], r8
	mov QWORD PTR [rdi+1768], r9
	mov QWORD PTR [rdi+1776], r10
	mov QWORD PTR [rdi+1784], r11
	mov rdx, QWORD PTR [rdi+1744]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1752]
	mulx r10, rax, QWORD PTR [rdi+1760]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1768]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1776]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1784]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1752]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1760]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1768]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1776]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1784]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1760]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1768]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1776]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1784]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1768]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1776]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1784]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1776]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1784]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1744]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1752]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1760]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1768]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1776]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1784]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	mov QWORD PTR [rdi+1864], r8
	mov QWORD PTR [rdi+1872], r9
	mov QWORD PTR [rdi+1880], rcx
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
	add r13, QWORD PTR [rdi+1840]
	adc r14, QWORD PTR [rdi+1848]
	adc r15, QWORD PTR [rdi+1856]
	adc r10, QWORD PTR [rdi+1864]
	adc r11, QWORD PTR [rdi+1872]
	adc r12, QWORD PTR [rdi+1880]
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
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	mov QWORD PTR [rdi+1864], r10
	mov QWORD PTR [rdi+1872], r11
	mov QWORD PTR [rdi+1880], r12
	mov rdx, QWORD PTR [rdi+1696]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1704]
	mulx r10, rax, QWORD PTR [rdi+1712]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1728]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1736]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1704]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1736]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1736]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1720]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1736]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1728]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1736]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1696]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1704]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1712]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1720]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1728]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1736]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+2032], r13
	mov QWORD PTR [rdi+2040], r14
	mov QWORD PTR [rdi+2048], r15
	mov QWORD PTR [rdi+2056], r8
	mov QWORD PTR [rdi+2064], r9
	mov QWORD PTR [rdi+2072], rcx
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
	add r13, QWORD PTR [rdi+2032]
	adc r14, QWORD PTR [rdi+2040]
	adc r15, QWORD PTR [rdi+2048]
	adc r10, QWORD PTR [rdi+2056]
	adc r11, QWORD PTR [rdi+2064]
	adc r12, QWORD PTR [rdi+2072]
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
	mov QWORD PTR [rdi+2032], r13
	mov QWORD PTR [rdi+2040], r14
	mov QWORD PTR [rdi+2048], r15
	mov QWORD PTR [rdi+2056], r10
	mov QWORD PTR [rdi+2064], r11
	mov QWORD PTR [rdi+2072], r12
	mov rdx, QWORD PTR [rdi+2032]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1696]
	mulx r10, rax, QWORD PTR [rdi+1704]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1712]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1720]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1728]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+2040]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+2048]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+2056]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+2064]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+2072]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov QWORD PTR [rdi+2080], r14
	mov QWORD PTR [rdi+2088], r15
	mov QWORD PTR [rdi+2096], r8
	mov QWORD PTR [rdi+2104], r9
	mov QWORD PTR [rdi+2112], r10
	mov QWORD PTR [rdi+2120], r11
	mov rdx, QWORD PTR [rdi+352]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1696]
	mulx r10, rax, QWORD PTR [rdi+1704]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1712]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1720]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1728]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+360]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+368]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+376]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov rdx, QWORD PTR [rdi+392]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
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
	mov QWORD PTR [rdi+2032], r14
	mov QWORD PTR [rdi+2040], r15
	mov QWORD PTR [rdi+2048], r8
	mov QWORD PTR [rdi+2056], r9
	mov QWORD PTR [rdi+2064], r10
	mov QWORD PTR [rdi+2072], r11
	mov r8, QWORD PTR [rdi+2080]
	mov r9, QWORD PTR [rdi+2088]
	mov r10, QWORD PTR [rdi+2096]
	mov r11, QWORD PTR [rdi+2104]
	mov r12, QWORD PTR [rdi+2112]
	mov r13, QWORD PTR [rdi+2120]
	mov r14d, 0
	add r8, QWORD PTR [rdi+2032]
	adc r9, QWORD PTR [rdi+2040]
	adc r10, QWORD PTR [rdi+2048]
	adc r11, QWORD PTR [rdi+2056]
	adc r12, QWORD PTR [rdi+2064]
	adc r13, QWORD PTR [rdi+2072]
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
	mov QWORD PTR [rdi+1888], r8
	mov QWORD PTR [rdi+1896], r9
	mov QWORD PTR [rdi+1904], r10
	mov QWORD PTR [rdi+1912], r11
	mov QWORD PTR [rdi+1920], r12
	mov QWORD PTR [rdi+1928], r13
	mov r8, QWORD PTR [rdi+1888]
	mov r9, QWORD PTR [rdi+1896]
	mov r10, QWORD PTR [rdi+1904]
	mov r11, QWORD PTR [rdi+1912]
	mov r12, QWORD PTR [rdi+1920]
	mov r13, QWORD PTR [rdi+1928]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1984]
	adc r9, QWORD PTR [rdi+1992]
	adc r10, QWORD PTR [rdi+2000]
	adc r11, QWORD PTR [rdi+2008]
	adc r12, QWORD PTR [rdi+2016]
	adc r13, QWORD PTR [rdi+2024]
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
	mov QWORD PTR [rdi+2080], r8
	mov QWORD PTR [rdi+2088], r9
	mov QWORD PTR [rdi+2096], r10
	mov QWORD PTR [rdi+2104], r11
	mov QWORD PTR [rdi+2112], r12
	mov QWORD PTR [rdi+2120], r13
	mov r8, QWORD PTR [rdi+1840]
	mov r9, QWORD PTR [rdi+1848]
	mov r10, QWORD PTR [rdi+1856]
	mov r11, QWORD PTR [rdi+1864]
	mov r12, QWORD PTR [rdi+1872]
	mov r13, QWORD PTR [rdi+1880]
	sub r8, QWORD PTR [rdi+2080]
	sbb r9, QWORD PTR [rdi+2088]
	sbb r10, QWORD PTR [rdi+2096]
	sbb r11, QWORD PTR [rdi+2104]
	sbb r12, QWORD PTR [rdi+2112]
	sbb r13, QWORD PTR [rdi+2120]
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
	mov QWORD PTR [rdi+2032], r8
	mov QWORD PTR [rdi+2040], r9
	mov QWORD PTR [rdi+2048], r10
	mov QWORD PTR [rdi+2056], r11
	mov QWORD PTR [rdi+2064], r12
	mov QWORD PTR [rdi+2072], r13
	mov rdx, QWORD PTR [rdi+2032]
	or rdx, QWORD PTR [rdi+2040]
	or rdx, QWORD PTR [rdi+2048]
	or rdx, QWORD PTR [rdi+2056]
	or rdx, QWORD PTR [rdi+2064]
	or rdx, QWORD PTR [rdi+2072]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+448]
	mov rdx, QWORD PTR [rdi+1696]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1888], rax
	mov rax, QWORD PTR [rdi+456]
	mov rdx, QWORD PTR [rdi+1704]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1896], rax
	mov rax, QWORD PTR [rdi+464]
	mov rdx, QWORD PTR [rdi+1712]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1904], rax
	mov rax, QWORD PTR [rdi+472]
	mov rdx, QWORD PTR [rdi+1720]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1912], rax
	mov rax, QWORD PTR [rdi+480]
	mov rdx, QWORD PTR [rdi+1728]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1920], rax
	mov rax, QWORD PTR [rdi+488]
	mov rdx, QWORD PTR [rdi+1736]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1928], rax
	mov rax, QWORD PTR [rdi+496]
	mov rdx, QWORD PTR [rdi+1744]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2128], rax
	mov rax, QWORD PTR [rdi+504]
	mov rdx, QWORD PTR [rdi+1752]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2136], rax
	mov rax, QWORD PTR [rdi+512]
	mov rdx, QWORD PTR [rdi+1760]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2144], rax
	mov rax, QWORD PTR [rdi+520]
	mov rdx, QWORD PTR [rdi+1768]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2152], rax
	mov rax, QWORD PTR [rdi+528]
	mov rdx, QWORD PTR [rdi+1776]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2160], rax
	mov rax, QWORD PTR [rdi+536]
	mov rdx, QWORD PTR [rdi+1784]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2168], rax
	movq rbx, xmm0
	movq rbp, xmm1
	movq r12, xmm2
	movq r13, xmm3
	movq r14, xmm4
	movq r15, xmm5
	ret
	.p2align 6
