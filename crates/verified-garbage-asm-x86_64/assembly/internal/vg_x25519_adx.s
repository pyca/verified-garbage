// The functions of `src/internal/vg_x25519_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519_adx:
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
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+224]
	mulx r10, rax, QWORD PTR [rdi+232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+248]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+248]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+248]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+248]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+128]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+192]
	mulx r10, rax, QWORD PTR [rdi+200]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+208]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+216]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+136]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+216]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+144]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+216]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+152]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+216]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+320]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+328]
	mulx r11, rax, QWORD PTR [rdi+336]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+344]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+328]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+336]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+344]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+336]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+344]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+320]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+328]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+336]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+344]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+104]
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+120]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+96]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+104]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+112]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+120]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+192]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+200]
	mulx r11, rax, QWORD PTR [rdi+208]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+216]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+200]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+216]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+208]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+216]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+192]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+200]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+208]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+216]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+160]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+168]
	mulx r11, rax, QWORD PTR [rdi+176]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+184]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+168]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+184]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+176]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+184]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+160]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+168]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+176]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+184]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov edx, 121665
	mov r8, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+120]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, QWORD PTR [rdi+312]
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
	mov edx, 38
	mulx rcx, rax, r12
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+320]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+96]
	mulx r10, rax, QWORD PTR [rdi+104]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+328]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+336]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+344]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+120]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+64]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+192]
	mulx r10, rax, QWORD PTR [rdi+200]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+208]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+216]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+72]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+216]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+80]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+216]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+88]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+216]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+128]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+136]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+144]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+152]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+224]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+232]
	mulx r11, rax, QWORD PTR [rdi+240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+248]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+248]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+240]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+248]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+224]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+232]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+240]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+248]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+264]
	mulx r11, rax, QWORD PTR [rdi+272]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+280]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+280]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+280]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+256]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+264]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+272]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+280]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov edx, 121665
	mov r8, QWORD PTR [rdi+224]
	mov r9, QWORD PTR [rdi+232]
	mov r10, QWORD PTR [rdi+240]
	mov r11, QWORD PTR [rdi+248]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, QWORD PTR [rdi+312]
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
	mov edx, 38
	mulx rcx, rax, r12
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+224]
	mulx r10, rax, QWORD PTR [rdi+232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+248]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+248]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+248]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+248]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+128]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+136]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+144]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+152]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+224]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+232]
	mulx r11, rax, QWORD PTR [rdi+240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+248]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+248]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+240]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+248]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+224]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+232]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+240]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+248]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+264]
	mulx r11, rax, QWORD PTR [rdi+272]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+280]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+280]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+280]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+256]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+264]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+272]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+280]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov edx, 121665
	mov r8, QWORD PTR [rdi+224]
	mov r9, QWORD PTR [rdi+232]
	mov r10, QWORD PTR [rdi+240]
	mov r11, QWORD PTR [rdi+248]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, QWORD PTR [rdi+312]
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
	mov edx, 38
	mulx rcx, rax, r12
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+224]
	mulx r10, rax, QWORD PTR [rdi+232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+248]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+248]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+248]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+248]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+128]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+136]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+144]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+152]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+224]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+232]
	mulx r11, rax, QWORD PTR [rdi+240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+248]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+248]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+240]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+248]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+224]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+232]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+240]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+248]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+264]
	mulx r11, rax, QWORD PTR [rdi+272]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+280]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+280]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+280]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+256]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+264]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+272]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+280]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov edx, 121665
	mov r8, QWORD PTR [rdi+224]
	mov r9, QWORD PTR [rdi+232]
	mov r10, QWORD PTR [rdi+240]
	mov r11, QWORD PTR [rdi+248]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, QWORD PTR [rdi+312]
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
	mov edx, 38
	mulx rcx, rax, r12
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+224]
	mulx r10, rax, QWORD PTR [rdi+232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+248]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+248]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+248]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+248]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+128]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+136]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+144]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+152]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+96]
	mulx r10, rax, QWORD PTR [rdi+104]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+120]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
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
