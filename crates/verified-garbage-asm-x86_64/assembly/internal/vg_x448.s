// The functions of `src/internal/vg_x448.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448:
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov QWORD PTR [rcx+24], r13
	mov QWORD PTR [rcx+32], r14
	mov QWORD PTR [rcx+40], r15
	mov r15, rdi
	mov rdi, rcx
	mov r8, QWORD PTR [rdx]
	mov r9, QWORD PTR [rdx+8]
	mov r10, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	mov r12, QWORD PTR [rdx+32]
	mov r13, QWORD PTR [rdx+40]
	mov r14, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov eax, 0
	mov edx, 1
	mov QWORD PTR [rdi+128], rdx
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+320], rdx
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+48], rax
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rsi+rbx*1]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2048], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2049], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2050], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2051], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2052], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2053], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2054], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2055], dl
	add rbx, 1
	cmp rbx, 56
	jne 20b
	mov eax, 0
	mov BYTE PTR [rdi+2048], al
	mov BYTE PTR [rdi+2049], al
	mov eax, 1
	mov BYTE PTR [rdi+2495], al
	mov rsi, r15
	mov ebx, 448
21:
	sub rbx, 1
	movzx eax, BYTE PTR [rdi+rbx*1+2048]
	mov rdx, QWORD PTR [rdi+48]
	xor rdx, rax
	mov QWORD PTR [rdi+48], rax
	mov ecx, 0
	sub rcx, rdx
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+200]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+216]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+224]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+232]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+240]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+368], rdx
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	add r8, QWORD PTR [rdi+192]
	adc r9, QWORD PTR [rdi+200]
	adc r10, QWORD PTR [rdi+208]
	adc r11, QWORD PTR [rdi+216]
	adc r12, QWORD PTR [rdi+224]
	adc r13, QWORD PTR [rdi+232]
	adc r14, QWORD PTR [rdi+240]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov QWORD PTR [rdi+416], r12
	mov QWORD PTR [rdi+424], r13
	mov QWORD PTR [rdi+432], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	sub r8, QWORD PTR [rdi+192]
	sbb r9, QWORD PTR [rdi+200]
	sbb r10, QWORD PTR [rdi+208]
	sbb r11, QWORD PTR [rdi+216]
	sbb r12, QWORD PTR [rdi+224]
	sbb r13, QWORD PTR [rdi+232]
	sbb r14, QWORD PTR [rdi+240]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+448], r8
	mov QWORD PTR [rdi+456], r9
	mov QWORD PTR [rdi+464], r10
	mov QWORD PTR [rdi+472], r11
	mov QWORD PTR [rdi+480], r12
	mov QWORD PTR [rdi+488], r13
	mov QWORD PTR [rdi+496], r14
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	add r8, QWORD PTR [rdi+320]
	adc r9, QWORD PTR [rdi+328]
	adc r10, QWORD PTR [rdi+336]
	adc r11, QWORD PTR [rdi+344]
	adc r12, QWORD PTR [rdi+352]
	adc r13, QWORD PTR [rdi+360]
	adc r14, QWORD PTR [rdi+368]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r14
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	sub r8, QWORD PTR [rdi+320]
	sbb r9, QWORD PTR [rdi+328]
	sbb r10, QWORD PTR [rdi+336]
	sbb r11, QWORD PTR [rdi+344]
	sbb r12, QWORD PTR [rdi+352]
	sbb r13, QWORD PTR [rdi+360]
	sbb r14, QWORD PTR [rdi+368]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	mov r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+472]
	mov r12, QWORD PTR [rdi+480]
	mov r13, QWORD PTR [rdi+488]
	mov r14, QWORD PTR [rdi+496]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov QWORD PTR [rdi+736], r12
	mov QWORD PTR [rdi+744], r13
	mov QWORD PTR [rdi+752], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+576]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+584]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+576]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+584]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+592]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+584]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+592]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+600]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+576]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+584]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+592]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+600]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+608]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+576]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+584]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+592]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+600]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+608]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+616]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+584]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+592]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+600]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+608]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+616]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+624]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+584]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+592]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+600]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+608]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+616]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+624]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+592]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+600]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+608]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+616]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+624]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+600]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+608]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+616]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+624]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+608]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+616]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+624]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+616]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+624]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+624]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+472]
	mov r12, QWORD PTR [rdi+480]
	mov r13, QWORD PTR [rdi+488]
	mov r14, QWORD PTR [rdi+496]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+512]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+512]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+520]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+512]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+520]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+528]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+512]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+520]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+528]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+536]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+512]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+520]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+528]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+536]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+544]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+512]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+520]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+528]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+536]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+544]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+552]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+512]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+520]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+528]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+536]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+544]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+552]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+560]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+520]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+528]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+536]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+544]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+552]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+560]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+528]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+536]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+544]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+552]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+560]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+536]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+544]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+552]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+560]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+544]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+552]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+560]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+552]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+560]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+560]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	mov r12, QWORD PTR [rdi+672]
	mov r13, QWORD PTR [rdi+680]
	mov r14, QWORD PTR [rdi+688]
	sub r8, QWORD PTR [rdi+704]
	sbb r9, QWORD PTR [rdi+712]
	sbb r10, QWORD PTR [rdi+720]
	sbb r11, QWORD PTR [rdi+728]
	sbb r12, QWORD PTR [rdi+736]
	sbb r13, QWORD PTR [rdi+744]
	sbb r14, QWORD PTR [rdi+752]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+768], r8
	mov QWORD PTR [rdi+776], r9
	mov QWORD PTR [rdi+784], r10
	mov QWORD PTR [rdi+792], r11
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb r12, QWORD PTR [rdi+928]
	sbb r13, QWORD PTR [rdi+936]
	sbb r14, QWORD PTR [rdi+944]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	sub r8, r15
	sbb r9, 0
	sbb r10, 0
	sbb r11, rax
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	add r8, QWORD PTR [rdi+896]
	adc r9, QWORD PTR [rdi+904]
	adc r10, QWORD PTR [rdi+912]
	adc r11, QWORD PTR [rdi+920]
	adc r12, QWORD PTR [rdi+928]
	adc r13, QWORD PTR [rdi+936]
	adc r14, QWORD PTR [rdi+944]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov ecx, 39081
	mov ebp, 0
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
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
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	mov r12, QWORD PTR [rdi+672]
	mov r13, QWORD PTR [rdi+680]
	mov r14, QWORD PTR [rdi+688]
	add r8, QWORD PTR [rdi+192]
	adc r9, QWORD PTR [rdi+200]
	adc r10, QWORD PTR [rdi+208]
	adc r11, QWORD PTR [rdi+216]
	adc r12, QWORD PTR [rdi+224]
	adc r13, QWORD PTR [rdi+232]
	adc r14, QWORD PTR [rdi+240]
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
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
	mov rax, QWORD PTR [rdi+64]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+64]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+72]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+64]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+72]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+80]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+72]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+80]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+88]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+64]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+72]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+80]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+88]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+96]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+64]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+72]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+80]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+88]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+96]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+104]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+72]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+80]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+88]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+96]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+104]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+112]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+72]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+80]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+88]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+96]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+104]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+112]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+80]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+88]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+96]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+104]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+112]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+88]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+96]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+104]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+112]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+96]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+104]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+112]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+104]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+112]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	mov r8, QWORD PTR [rdi+704]
	mov r9, QWORD PTR [rdi+712]
	mov r10, QWORD PTR [rdi+720]
	mov r11, QWORD PTR [rdi+728]
	mov r12, QWORD PTR [rdi+736]
	mov r13, QWORD PTR [rdi+744]
	mov r14, QWORD PTR [rdi+752]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+640]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+640]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+648]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+640]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+648]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+656]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+640]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+648]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+656]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+664]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+640]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+648]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+656]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+664]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+672]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+640]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+648]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+656]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+664]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+672]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+680]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+640]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+648]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+656]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+664]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+672]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+680]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+688]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+648]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+656]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+664]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+672]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+680]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+688]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+656]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+664]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+672]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+680]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+688]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+664]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+672]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+680]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+688]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+672]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+680]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+688]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+680]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+688]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+688]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+768]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+768]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+776]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+768]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+776]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+784]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+768]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+776]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+784]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+792]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+768]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+776]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+784]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+792]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+800]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+768]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+776]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+784]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+792]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+800]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+808]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+768]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+776]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+784]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+792]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+800]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+808]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+816]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+776]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+784]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+792]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+800]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+808]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+816]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+784]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+792]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+800]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+808]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+816]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+792]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+800]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+808]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+816]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+800]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+808]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+816]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+808]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+816]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+816]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	test rbx, rbx
	jne 21b
	mov rdx, QWORD PTR [rdi+48]
	mov ecx, 0
	sub rcx, rdx
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+200]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+216]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+224]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+232]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+240]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+368], rdx
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	call {vg_gf448_r64_pow223}
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	mov r14, QWORD PTR [rdi+1456]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r14
	mov ebx, 224
22:
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	mov r14, QWORD PTR [rdi+1456]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r14
	sub rbx, 1
	jne 22b
	mov r8, QWORD PTR [rdi+1344]
	mov r9, QWORD PTR [rdi+1352]
	mov r10, QWORD PTR [rdi+1360]
	mov r11, QWORD PTR [rdi+1368]
	mov r12, QWORD PTR [rdi+1376]
	mov r13, QWORD PTR [rdi+1384]
	mov r14, QWORD PTR [rdi+1392]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1344], r8
	mov QWORD PTR [rdi+1352], r9
	mov QWORD PTR [rdi+1360], r10
	mov QWORD PTR [rdi+1368], r11
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r14
	mov ebx, 1
23:
	mov r8, QWORD PTR [rdi+1344]
	mov r9, QWORD PTR [rdi+1352]
	mov r10, QWORD PTR [rdi+1360]
	mov r11, QWORD PTR [rdi+1368]
	mov r12, QWORD PTR [rdi+1376]
	mov r13, QWORD PTR [rdi+1384]
	mov r14, QWORD PTR [rdi+1392]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, r8
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, r8
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, r8
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, r8
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, r8
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r9
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, r8
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r9
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r10
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, r8
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r9
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r10
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r11
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, r9
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r10
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r11
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, r10
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r11
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, r12
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, r11
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, r12
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, r12
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, r13
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, r13
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, r14
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1344], r8
	mov QWORD PTR [rdi+1352], r9
	mov QWORD PTR [rdi+1360], r10
	mov QWORD PTR [rdi+1368], r11
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r14
	sub rbx, 1
	jne 23b
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1344]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1344]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1352]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1344]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1352]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1360]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1344]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1352]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1368]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1344]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1352]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1360]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1368]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1376]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1344]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1352]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1360]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1368]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1376]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1384]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1344]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1352]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1368]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1376]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1384]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1392]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1352]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1360]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1368]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1376]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1384]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1392]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1360]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1368]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1376]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1384]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1392]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1368]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1376]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1384]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1392]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1376]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1384]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1392]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1384]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1392]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1392]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1344], r8
	mov QWORD PTR [rdi+1352], r9
	mov QWORD PTR [rdi+1360], r10
	mov QWORD PTR [rdi+1368], r11
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r14
	mov r8, QWORD PTR [rdi+1344]
	mov r9, QWORD PTR [rdi+1352]
	mov r10, QWORD PTR [rdi+1360]
	mov r11, QWORD PTR [rdi+1368]
	mov r12, QWORD PTR [rdi+1376]
	mov r13, QWORD PTR [rdi+1384]
	mov r14, QWORD PTR [rdi+1392]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1416]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1424]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1432]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1440]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1448]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r14
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	mov r14, QWORD PTR [rdi+1456]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+128]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+128]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+136]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+128]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+136]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+144]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+128]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+136]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+144]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+152]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+128]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+136]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+144]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+152]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+160]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+128]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+136]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+144]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+152]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+160]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+168]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+128]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+136]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+144]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+152]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+160]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+168]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+176]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+136]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+144]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+152]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+160]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+168]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+176]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+144]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+152]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+160]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+168]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+176]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+152]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+160]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+168]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+176]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+160]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+168]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+176]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+168]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+176]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+176]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1632], r15
	mov r15d, 0
	mov QWORD PTR [rdi+1640], rcx
	mov ecx, 0
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r15d, 1
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+128]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+136]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+144]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+152]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+160]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+168]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+176]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
