// The functions of `src/internal/vg_x25519.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519:
	mov r8, QWORD PTR [rdx]
	mov r9, QWORD PTR [rdx+8]
	mov r10, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	movabs rax, 9223372036854775807
	and r11, rax
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov QWORD PTR [rcx+24], r13
	mov QWORD PTR [rcx+32], r14
	mov QWORD PTR [rcx+40], r15
	mov r12, rdi
	mov rdi, rcx
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 0
	mov edx, 1
	mov QWORD PTR [rdi+96], rdx
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+192], rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+640], rax
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rsi+rbx*1]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+768], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+769], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+770], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+771], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+772], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+773], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+774], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+775], dl
	add rbx, 1
	cmp rbx, 32
	jne 20b
	mov eax, 0
	mov BYTE PTR [rdi+768], al
	mov BYTE PTR [rdi+769], al
	mov BYTE PTR [rdi+770], al
	mov eax, 1
	mov BYTE PTR [rdi+1022], al
	mov rsi, r12
	mov ebx, 255
21:
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+160]
	sub r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+168]
	sbb r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+176]
	sbb r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+184]
	sbb r11, QWORD PTR [rdi+216]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+96]
	add r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+104]
	adc r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+112]
	adc r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+120]
	adc r11, QWORD PTR [rdi+152]
	cmovae rax, rcx
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+96]
	sub r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+104]
	sbb r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+112]
	sbb r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+120]
	sbb r11, QWORD PTR [rdi+152]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+160]
	add r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+168]
	adc r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+176]
	adc r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+184]
	adc r11, QWORD PTR [rdi+216]
	cmovae rax, rcx
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov r14, QWORD PTR [rdi+256]
	mov r15, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+272]
	mov rbp, QWORD PTR [rdi+280]
	mov rax, QWORD PTR [rdi+224]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+224]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+232]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+232]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+240]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+224]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+240]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+248]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+232]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+248]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+240]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	sub rbx, 1
	movzx eax, BYTE PTR [rdi+rbx*1+768]
	cmp rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+128]
	mov r13, QWORD PTR [rdi+136]
	mov r14, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+152]
	cmove r8, r12
	cmove r9, r13
	cmove r10, r14
	cmove r11, r15
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov r15, QWORD PTR [rdi+248]
	cmove r8, r12
	cmove r9, r13
	cmove r10, r14
	cmove r11, r15
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r14, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov rbp, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+192]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+192]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+200]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+200]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+208]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+192]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+208]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+216]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+200]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+216]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+208]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov rcx, QWORD PTR [rdi+328]
	mov rbp, QWORD PTR [rdi+336]
	mov r15, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+320]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+320]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+320]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+328]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+328]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+336]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+320]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+328]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+336]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+344]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+288]
	sub r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+296]
	sbb r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+304]
	sbb r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+312]
	sbb r11, QWORD PTR [rdi+184]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov rcx, QWORD PTR [rdi+104]
	mov rbp, QWORD PTR [rdi+112]
	mov r15, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+96]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+96]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+104]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+104]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+112]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+96]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+112]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+120]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+288]
	add r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+296]
	adc r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+304]
	adc r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+312]
	adc r11, QWORD PTR [rdi+184]
	cmovae rax, rcx
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov rcx, QWORD PTR [rdi+200]
	mov rbp, QWORD PTR [rdi+208]
	mov r15, QWORD PTR [rdi+216]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+192]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+192]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+200]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+200]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+208]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+192]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+208]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+216]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+96]
	sub r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+104]
	sbb r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+112]
	sbb r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+120]
	sbb r11, QWORD PTR [rdi+344]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rcx, QWORD PTR [rdi+168]
	mov rbp, QWORD PTR [rdi+176]
	mov r15, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+160]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+160]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+168]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+168]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+176]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+160]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+168]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+176]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+184]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov ecx, 121665
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r11, rax
	adc r12, rdx
	add r8, QWORD PTR [rdi+96]
	adc r9, QWORD PTR [rdi+104]
	adc r10, QWORD PTR [rdi+112]
	adc r11, QWORD PTR [rdi+120]
	adc r12, 0
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov r14, QWORD PTR [rdi+320]
	mov r15, QWORD PTR [rdi+328]
	mov rcx, QWORD PTR [rdi+336]
	mov rbp, QWORD PTR [rdi+344]
	mov rax, QWORD PTR [rdi+96]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+96]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+104]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+104]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+112]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+96]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+112]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+120]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+104]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+120]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+112]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+120]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r14, QWORD PTR [rdi+64]
	mov r15, QWORD PTR [rdi+72]
	mov rcx, QWORD PTR [rdi+80]
	mov rbp, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+192]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+200]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+200]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+208]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+192]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+208]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+216]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+200]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+216]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+208]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov r14, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov rbp, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+288]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+288]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+296]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+296]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+304]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+288]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+304]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+312]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+296]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+312]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+304]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	cmp rbx, 3
	jne 21b
	mov rax, QWORD PTR [rdi+640]
	cmp rax, 0
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	mov r15, QWORD PTR [rdi+120]
	cmove r8, r12
	cmove r9, r13
	cmove r10, r14
	cmove r11, r15
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+128]
	mov r13, QWORD PTR [rdi+136]
	mov r14, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+152]
	cmove r8, r12
	cmove r9, r13
	cmove r10, r14
	cmove r11, r15
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+96]
	add r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+104]
	adc r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+112]
	adc r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+120]
	adc r11, QWORD PTR [rdi+152]
	cmovae rax, rcx
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+96]
	sub r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+104]
	sbb r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+112]
	sbb r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+120]
	sbb r11, QWORD PTR [rdi+152]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov rcx, QWORD PTR [rdi+232]
	mov rbp, QWORD PTR [rdi+240]
	mov r15, QWORD PTR [rdi+248]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+224]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+224]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+232]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+232]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+240]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+224]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+232]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+240]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+248]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov rcx, QWORD PTR [rdi+264]
	mov rbp, QWORD PTR [rdi+272]
	mov r15, QWORD PTR [rdi+280]
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+256]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+256]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+264]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+264]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+272]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+256]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+272]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+280]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+248]
	sbb r11, QWORD PTR [rdi+280]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov ecx, 121665
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r11, rax
	adc r12, rdx
	add r8, QWORD PTR [rdi+224]
	adc r9, QWORD PTR [rdi+232]
	adc r10, QWORD PTR [rdi+240]
	adc r11, QWORD PTR [rdi+248]
	adc r12, 0
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov r14, QWORD PTR [rdi+256]
	mov r15, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+272]
	mov rbp, QWORD PTR [rdi+280]
	mov rax, QWORD PTR [rdi+224]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+224]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+232]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+232]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+240]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+224]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+240]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+248]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+232]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+248]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+240]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r14, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov rbp, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+288]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+288]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+296]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+296]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+304]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+288]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+304]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+312]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+296]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+312]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+304]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+96]
	add r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+104]
	adc r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+112]
	adc r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+120]
	adc r11, QWORD PTR [rdi+152]
	cmovae rax, rcx
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+96]
	sub r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+104]
	sbb r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+112]
	sbb r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+120]
	sbb r11, QWORD PTR [rdi+152]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov rcx, QWORD PTR [rdi+232]
	mov rbp, QWORD PTR [rdi+240]
	mov r15, QWORD PTR [rdi+248]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+224]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+224]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+232]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+232]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+240]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+224]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+232]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+240]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+248]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov rcx, QWORD PTR [rdi+264]
	mov rbp, QWORD PTR [rdi+272]
	mov r15, QWORD PTR [rdi+280]
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+256]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+256]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+264]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+264]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+272]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+256]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+272]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+280]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+248]
	sbb r11, QWORD PTR [rdi+280]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov ecx, 121665
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r11, rax
	adc r12, rdx
	add r8, QWORD PTR [rdi+224]
	adc r9, QWORD PTR [rdi+232]
	adc r10, QWORD PTR [rdi+240]
	adc r11, QWORD PTR [rdi+248]
	adc r12, 0
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov r14, QWORD PTR [rdi+256]
	mov r15, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+272]
	mov rbp, QWORD PTR [rdi+280]
	mov rax, QWORD PTR [rdi+224]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+224]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+232]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+232]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+240]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+224]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+240]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+248]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+232]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+248]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+240]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r14, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov rbp, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+288]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+288]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+296]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+296]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+304]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+288]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+304]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+312]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+296]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+312]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+304]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+96]
	add r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+104]
	adc r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+112]
	adc r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+120]
	adc r11, QWORD PTR [rdi+152]
	cmovae rax, rcx
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+96]
	sub r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+104]
	sbb r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+112]
	sbb r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+120]
	sbb r11, QWORD PTR [rdi+152]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov rcx, QWORD PTR [rdi+232]
	mov rbp, QWORD PTR [rdi+240]
	mov r15, QWORD PTR [rdi+248]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+224]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+224]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+232]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+232]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+240]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+224]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+232]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+240]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+248]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov rcx, QWORD PTR [rdi+264]
	mov rbp, QWORD PTR [rdi+272]
	mov r15, QWORD PTR [rdi+280]
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+256]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+256]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+264]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+264]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+272]
	mul r15
	add r13, rax
	adc r14, rdx
	xor r15d, r15d
	add r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, QWORD PTR [rdi+256]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+272]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+280]
	mul rax
	add rcx, rcx
	adc r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	xor ecx, ecx
	mov eax, 38
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+248]
	sbb r11, QWORD PTR [rdi+280]
	cmovae rax, rcx
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov ecx, 121665
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r11, rax
	adc r12, rdx
	add r8, QWORD PTR [rdi+224]
	adc r9, QWORD PTR [rdi+232]
	adc r10, QWORD PTR [rdi+240]
	adc r11, QWORD PTR [rdi+248]
	adc r12, 0
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov r14, QWORD PTR [rdi+256]
	mov r15, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+272]
	mov rbp, QWORD PTR [rdi+280]
	mov rax, QWORD PTR [rdi+224]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+224]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+232]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+232]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+240]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+224]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+240]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+248]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+232]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+248]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+240]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r14, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov rbp, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+288]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+288]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+296]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+296]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+304]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+288]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+304]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+312]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+296]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+312]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+304]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov eax, 0
	mov QWORD PTR [rdi+640], rax
	mov rdx, QWORD PTR [rdi+640]
	mov ecx, 0
	sub rcx, rdx
	mov r8, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+120]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov r15, QWORD PTR [rdi+184]
	mov rax, r8
	xor rax, r12
	and rax, rcx
	xor r8, rax
	xor r12, rax
	mov rax, r9
	xor rax, r13
	and rax, rcx
	xor r9, rax
	xor r13, rax
	mov rax, r10
	xor rax, r14
	and rax, rcx
	xor r10, rax
	xor r14, rax
	mov rax, r11
	xor rax, r15
	and rax, rcx
	xor r11, rax
	xor r15, rax
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov QWORD PTR [rdi+184], r15
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+192]
	mov r13, QWORD PTR [rdi+200]
	mov r14, QWORD PTR [rdi+208]
	mov r15, QWORD PTR [rdi+216]
	mov rax, r8
	xor rax, r12
	and rax, rcx
	xor r8, rax
	xor r12, rax
	mov rax, r9
	xor rax, r13
	and rax, rcx
	xor r9, rax
	xor r13, rax
	mov rax, r10
	xor rax, r14
	and rax, rcx
	xor r10, rax
	xor r14, rax
	mov rax, r11
	xor rax, r15
	and rax, rcx
	xor r11, rax
	xor r15, rax
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+192], r12
	mov QWORD PTR [rdi+200], r13
	mov QWORD PTR [rdi+208], r14
	mov QWORD PTR [rdi+216], r15
	call {vg_gf25519_r64_invert}
	mov r14, QWORD PTR [rdi+544]
	mov r15, QWORD PTR [rdi+552]
	mov rcx, QWORD PTR [rdi+560]
	mov rbp, QWORD PTR [rdi+568]
	mov rax, QWORD PTR [rdi+96]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+96]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+104]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+104]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+112]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+96]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+112]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+120]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+104]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+120]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+112]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+120]
	mul rbp
	add r14, rax
	adc r15, rdx
	mov ecx, 38
	mov rax, r12
	mul rcx
	add r8, rax
	adc r9, rdx
	sbb rbp, rbp
	mov rax, r13
	mul rcx
	sub rdx, rbp
	add r9, rax
	adc r10, rdx
	sbb rbp, rbp
	mov rax, r14
	mul rcx
	sub rdx, rbp
	add r10, rax
	adc r11, rdx
	sbb rbp, rbp
	mov rax, r15
	mul rcx
	sub rdx, rbp
	add r11, rax
	adc rdx, 0
	mov r12, rdx
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r8, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+120]
	mov rax, r11
	shr rax, 63
	movabs rdx, 9223372036854775807
	and r11, rdx
	mov ecx, 0
	sub rcx, rax
	and rcx, 19
	add r8, rcx
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov r12, r8
	add r12, 19
	mov r13, r9
	adc r13, 0
	mov r14, r10
	adc r14, 0
	mov r15, r11
	adc r15, 0
	mov rax, r15
	shr rax, 63
	and r15, rdx
	mov ecx, 0
	sub rcx, rax
	xor r12, r8
	and r12, rcx
	xor r8, r12
	xor r13, r9
	and r13, rcx
	xor r9, r13
	xor r14, r10
	and r14, rcx
	xor r10, r14
	xor r15, r11
	and r15, rcx
	xor r11, r15
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	ret
	.p2align 6
