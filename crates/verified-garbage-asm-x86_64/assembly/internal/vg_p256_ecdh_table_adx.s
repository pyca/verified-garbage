// The functions of `src/internal/vg_p256_ecdh_table_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_ecdh_table_adx:
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+5368], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5384], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5392], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5400], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5408], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5416], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5424], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5432], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5440], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5448], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5456], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5464], rax
	mov ebx, 1
	mov rax, rbx
	sub rax, 1
	mov ecx, 160
	mul rcx
	mov rdx, rdi
	add rdx, 2752
	add rdx, rax
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdx+120], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdx+128], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdx+136], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdx+144], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdx+152], rax
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+1288]
	mulx r11, rax, QWORD PTR [rdi+1296]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1304]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1304]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+1304]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1280]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+1288]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+1296]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+1304]
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
	mov rdx, QWORD PTR [rdi+1440]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+1448]
	mulx r11, rax, QWORD PTR [rdi+1456]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1464]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1448]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1464]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1456]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+1464]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1440]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+1448]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+1456]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+1464]
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
	mov rdx, r12
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
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
	mov rdx, r15
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
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1288]
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
	mov rdx, QWORD PTR [rdi+1296]
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
	mov rdx, QWORD PTR [rdi+1304]
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
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
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
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+800]
	mov r9, QWORD PTR [rdi+808]
	mov r10, QWORD PTR [rdi+816]
	mov r11, QWORD PTR [rdi+824]
	sub r8, QWORD PTR [rdi+224]
	sbb r9, QWORD PTR [rdi+232]
	sbb r10, QWORD PTR [rdi+240]
	sbb r11, QWORD PTR [rdi+248]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
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
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, QWORD PTR [rdi+928]
	adc r9, QWORD PTR [rdi+936]
	adc r10, QWORD PTR [rdi+944]
	adc r11, QWORD PTR [rdi+952]
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
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+936]
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+952]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+936]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+944]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+952]
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
	mov QWORD PTR [rdi+5312], r12
	mov QWORD PTR [rdi+5320], r13
	mov QWORD PTR [rdi+5328], r14
	mov QWORD PTR [rdi+5336], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov rdx, QWORD PTR [rdi+928]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+960]
	mulx r10, rax, QWORD PTR [rdi+968]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+976]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+984]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+960]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+968]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+984]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+960]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+968]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+984]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+952]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+960]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+968]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+984]
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
	mov QWORD PTR [rdi+5344], r12
	mov QWORD PTR [rdi+5352], r13
	mov QWORD PTR [rdi+5360], r14
	mov QWORD PTR [rdi+5368], r15
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
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
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
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
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
	mov r8, QWORD PTR [rdi+5344]
	mov r9, QWORD PTR [rdi+5352]
	mov r10, QWORD PTR [rdi+5360]
	mov r11, QWORD PTR [rdi+5368]
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
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov r8, QWORD PTR [rdi+1440]
	mov r9, QWORD PTR [rdi+1448]
	mov r10, QWORD PTR [rdi+1456]
	mov r11, QWORD PTR [rdi+1464]
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
	mov QWORD PTR [rdi+5376], r8
	mov QWORD PTR [rdi+5384], r9
	mov QWORD PTR [rdi+5392], r10
	mov QWORD PTR [rdi+5400], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+5384]
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5392]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+5400]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+5384]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+5392]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+5400]
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
	mov QWORD PTR [rdi+5408], r12
	mov QWORD PTR [rdi+5416], r13
	mov QWORD PTR [rdi+5424], r14
	mov QWORD PTR [rdi+5432], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5376]
	mulx r10, rax, QWORD PTR [rdi+5384]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5400]
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
	mov QWORD PTR [rdi+5440], r12
	mov QWORD PTR [rdi+5448], r13
	mov QWORD PTR [rdi+5456], r14
	mov QWORD PTR [rdi+5464], r15
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+5368], rax
20:
	add rbx, 1
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+800], r8
	mov QWORD PTR [rdi+808], r9
	mov QWORD PTR [rdi+816], r10
	mov QWORD PTR [rdi+824], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+808]
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+808]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+816]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+824]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+808]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+816]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+824]
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
	mov rdx, QWORD PTR [rdi+5376]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5384]
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
	mov rdx, QWORD PTR [rdi+5392]
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
	mov rdx, QWORD PTR [rdi+5400]
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
	mov QWORD PTR [rdi+5376], r12
	mov QWORD PTR [rdi+5384], r13
	mov QWORD PTR [rdi+5392], r14
	mov QWORD PTR [rdi+5400], r15
	mov rdx, QWORD PTR [rdi+608]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+616]
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
	mov rdx, QWORD PTR [rdi+624]
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
	mov rdx, QWORD PTR [rdi+632]
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
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov QWORD PTR [rdi+632], r15
	mov rdx, QWORD PTR [rdi+5312]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5320]
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
	mov rdx, QWORD PTR [rdi+5328]
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
	mov rdx, QWORD PTR [rdi+5336]
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
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	sub r8, QWORD PTR [rdi+5344]
	sbb r9, QWORD PTR [rdi+5352]
	sbb r10, QWORD PTR [rdi+5360]
	sbb r11, QWORD PTR [rdi+5368]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+936]
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+952]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+936]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+944]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+952]
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
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov rdx, QWORD PTR [rdi+640]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+864]
	mulx r10, rax, QWORD PTR [rdi+872]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+880]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+888]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+648]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+888]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+656]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+888]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+664]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+888]
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
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
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
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov rdx, QWORD PTR [rdi+928]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5344]
	mulx r10, rax, QWORD PTR [rdi+5352]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5360]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5368]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5352]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5360]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5368]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5344]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5352]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5360]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5368]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+952]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5344]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5352]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5360]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5368]
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
	mov QWORD PTR [rdi+5344], r12
	mov QWORD PTR [rdi+5352], r13
	mov QWORD PTR [rdi+5360], r14
	mov QWORD PTR [rdi+5368], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+640]
	sbb r9, QWORD PTR [rdi+648]
	sbb r10, QWORD PTR [rdi+656]
	sbb r11, QWORD PTR [rdi+664]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov rdx, QWORD PTR [rdi+5408]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5416]
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
	mov rdx, QWORD PTR [rdi+5424]
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
	mov rdx, QWORD PTR [rdi+5432]
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
	mov QWORD PTR [rdi+5408], r12
	mov QWORD PTR [rdi+5416], r13
	mov QWORD PTR [rdi+5424], r14
	mov QWORD PTR [rdi+5432], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5376]
	mulx r10, rax, QWORD PTR [rdi+5384]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5400]
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
	mov QWORD PTR [rdi+5440], r12
	mov QWORD PTR [rdi+5448], r13
	mov QWORD PTR [rdi+5456], r14
	mov QWORD PTR [rdi+5464], r15
	mov rax, rbx
	sub rax, 1
	mov ecx, 160
	mul rcx
	mov rdx, rdi
	add rdx, 2752
	add rdx, rax
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdx+120], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdx+128], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdx+136], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdx+144], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdx+152], rax
	cmp rbx, 16
	jne 20b
	ret
	.p2align 6
