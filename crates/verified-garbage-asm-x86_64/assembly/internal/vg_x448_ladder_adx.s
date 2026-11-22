// The functions of `src/internal/vg_x448_ladder_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448_ladder_adx:
	mov ebx, 448
20:
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
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+384]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+392]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+400]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+408]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+416]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+424]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+384]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+392]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+400]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+408]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+416]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+424]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+432]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1632]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1640]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1632], r8
	mov QWORD PTR [rdi+1640], r9
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
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+448]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+456]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+464]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+472]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+480]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+488]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+496]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+456]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+464]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+472]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+480]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+488]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+496]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+464]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+472]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+480]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+488]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+496]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+472]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+480]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+488]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+496]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+480]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+488]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+496]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+488]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+496]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+448]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+456]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+464]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+472]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+480]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+488]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+496]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1632]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1640]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1632], r8
	mov QWORD PTR [rdi+1640], r9
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+384]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+600]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+392]
	mov r8d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+400]
	mov r9d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+408]
	mov r10d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+416]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+600]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+424]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+600]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+432]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+600]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	mov QWORD PTR [rdi+1584], r14
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	mov QWORD PTR [rdi+1640], r13
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+448]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+512]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+520]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+528]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+536]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+456]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+512]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+520]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+528]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+536]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+464]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+512]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+520]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+528]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+536]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+472]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+512]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+520]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+528]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+536]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+480]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+512]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+520]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+528]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+536]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+488]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+512]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+520]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+528]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+536]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+496]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+512]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+520]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+528]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+536]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	mov QWORD PTR [rdi+1584], r14
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	mov QWORD PTR [rdi+1640], r13
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
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+320]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+328]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+336]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+344]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+352]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+360]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+328]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+336]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+344]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+352]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+360]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+336]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+352]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+360]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+344]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+352]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+360]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+352]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+360]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+360]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+320]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+328]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+336]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+344]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+352]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+360]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+368]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1632]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1640]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1632], r8
	mov QWORD PTR [rdi+1640], r9
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
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+256]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+280]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+264]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+280]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+272]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+280]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+280]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+288]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+296]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+256]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+264]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+272]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+280]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+288]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+296]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+304]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1632]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1640]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1632], r8
	mov QWORD PTR [rdi+1640], r9
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+320]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+328]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+336]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+344]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+352]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+360]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+368]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	mov QWORD PTR [rdi+1584], r14
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	mov QWORD PTR [rdi+1640], r13
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+704]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+664]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+712]
	mov r8d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+664]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+720]
	mov r9d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+664]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+728]
	mov r10d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+664]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+736]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+664]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+744]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+664]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+752]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+640]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+648]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+664]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	mov QWORD PTR [rdi+1584], r14
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	mov QWORD PTR [rdi+1640], r13
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+192]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+768]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+776]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+200]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+768]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+776]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+208]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+768]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+776]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+216]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+768]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+776]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+224]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+768]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+776]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+232]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+768]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+776]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+240]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+768]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+776]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	mov QWORD PTR [rdi+1584], r14
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	mov QWORD PTR [rdi+1640], r13
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
	jne 20b
	ret
	.p2align 6
