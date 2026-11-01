// The functions of `src/internal/vg_ed448_scalar_mul_add.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_mul_add:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov QWORD PTR [r8+48], rdi
	mov QWORD PTR [r8+56], rsi
	mov QWORD PTR [r8+64], rdx
	mov QWORD PTR [r8+72], rcx
	mov rdi, r8
	movabs r8, -2556006723728458995
	movabs r9, -2408513697996967766
	movabs r10, 4301259484579875183
	movabs r11, 2201345046
	movabs r12, 0
	movabs r13, 0
	movabs r14, -4611686018427387904
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov rsi, QWORD PTR [rdi+64]
	movzx r8d, BYTE PTR [rsi+56]
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov ebx, 56
20:
	sub rbx, 8
	mov rax, QWORD PTR [rsi+rbx*1]
	mov rcx, r13
	shr rcx, 62
	mov rbp, r14
	ror rbp, 62
	add rcx, rbp
	movabs rbp, 4611686018427387903
	and r13, rbp
	mov r14, r13
	mov r13, r12
	mov r12, r11
	mov r11, r10
	mov r10, r9
	mov r9, r8
	mov r8, rax
	mov ebp, 0
	movabs rax, -2556006723728458995
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, -2408513697996967766
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 4301259484579875183
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 2201345046
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	adc r12, QWORD PTR [rdi+160]
	adc r13, QWORD PTR [rdi+168]
	adc r14, QWORD PTR [rdi+176]
	sbb r15, r15
	mov rax, QWORD PTR [rdi+192]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+200]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+208]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+216]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+224]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+232]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+240]
	xor r14, rax
	and r14, r15
	xor r14, rax
	test rbx, rbx
	jne 20b
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov rsi, QWORD PTR [rdi+72]
	movzx r8d, BYTE PTR [rsi+56]
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov ebx, 56
21:
	sub rbx, 8
	mov rax, QWORD PTR [rsi+rbx*1]
	mov rcx, r13
	shr rcx, 62
	mov rbp, r14
	ror rbp, 62
	add rcx, rbp
	movabs rbp, 4611686018427387903
	and r13, rbp
	mov r14, r13
	mov r13, r12
	mov r12, r11
	mov r11, r10
	mov r10, r9
	mov r9, r8
	mov r8, rax
	mov ebp, 0
	movabs rax, -2556006723728458995
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, -2408513697996967766
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 4301259484579875183
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 2201345046
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	adc r12, QWORD PTR [rdi+160]
	adc r13, QWORD PTR [rdi+168]
	adc r14, QWORD PTR [rdi+176]
	sbb r15, r15
	mov rax, QWORD PTR [rdi+192]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+200]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+208]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+216]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+224]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+232]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+240]
	xor r14, rax
	and r14, r15
	xor r14, rax
	test rbx, rbx
	jne 21b
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	mov rsi, QWORD PTR [rdi+56]
	movzx r8d, BYTE PTR [rsi+56]
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov ebx, 56
22:
	sub rbx, 8
	mov rax, QWORD PTR [rsi+rbx*1]
	mov rcx, r13
	shr rcx, 62
	mov rbp, r14
	ror rbp, 62
	add rcx, rbp
	movabs rbp, 4611686018427387903
	and r13, rbp
	mov r14, r13
	mov r13, r12
	mov r12, r11
	mov r11, r10
	mov r10, r9
	mov r9, r8
	mov r8, rax
	mov ebp, 0
	movabs rax, -2556006723728458995
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, -2408513697996967766
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 4301259484579875183
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 2201345046
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	adc r12, QWORD PTR [rdi+160]
	adc r13, QWORD PTR [rdi+168]
	adc r14, QWORD PTR [rdi+176]
	sbb r15, r15
	mov rax, QWORD PTR [rdi+192]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+200]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+208]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+216]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+224]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+232]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+240]
	xor r14, rax
	and r14, r15
	xor r14, rax
	test rbx, rbx
	jne 22b
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov QWORD PTR [rdi+416], r12
	mov QWORD PTR [rdi+424], r13
	mov QWORD PTR [rdi+432], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+256]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+264]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+256]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+264]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+272]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+264]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+272]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+280]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+256]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+264]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+272]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+288]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+256]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+264]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+272]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+280]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+288]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+296]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+264]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+272]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+280]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+288]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+296]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+304]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+264]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+272]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+288]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+296]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+304]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+272]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+280]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+288]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+296]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+304]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+280]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+288]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+296]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+304]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+288]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+296]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+304]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+296]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+304]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+304]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov rsi, rdi
	add rsi, 1536
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov ebx, 112
23:
	sub rbx, 8
	mov rax, QWORD PTR [rsi+rbx*1]
	mov rcx, r13
	shr rcx, 62
	mov rbp, r14
	ror rbp, 62
	add rcx, rbp
	movabs rbp, 4611686018427387903
	and r13, rbp
	mov r14, r13
	mov r13, r12
	mov r12, r11
	mov r11, r10
	mov r10, r9
	mov r9, r8
	mov r8, rax
	mov ebp, 0
	movabs rax, -2556006723728458995
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, -2408513697996967766
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 4301259484579875183
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 2201345046
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	adc r12, QWORD PTR [rdi+160]
	adc r13, QWORD PTR [rdi+168]
	adc r14, QWORD PTR [rdi+176]
	sbb r15, r15
	mov rax, QWORD PTR [rdi+192]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+200]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+208]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+216]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+224]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+232]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+240]
	xor r14, rax
	and r14, r15
	xor r14, rax
	test rbx, rbx
	jne 23b
	add r8, QWORD PTR [rdi+384]
	adc r9, QWORD PTR [rdi+392]
	adc r10, QWORD PTR [rdi+400]
	adc r11, QWORD PTR [rdi+408]
	adc r12, QWORD PTR [rdi+416]
	adc r13, QWORD PTR [rdi+424]
	adc r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	adc r12, QWORD PTR [rdi+160]
	adc r13, QWORD PTR [rdi+168]
	adc r14, QWORD PTR [rdi+176]
	sbb r15, r15
	mov rax, QWORD PTR [rdi+192]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+200]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+208]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+216]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+224]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+232]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+240]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov QWORD PTR [rax+32], r12
	mov QWORD PTR [rax+40], r13
	mov QWORD PTR [rax+48], r14
	mov ecx, 0
	mov BYTE PTR [rax+56], cl
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
