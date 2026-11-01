// The functions of `src/internal/vg_ed25519_r64_add_cached_proj_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_r64_add_cached_proj_adx:
	movq xmm0, rbp
	movq xmm1, r12
	movq xmm2, r13
	movq xmm3, r14
	movq xmm4, r15
	mov r8, QWORD PTR [rdi+96]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+104]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+112]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+120]
	sbb r11, QWORD PTR [rdi+88]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov rdx, QWORD PTR [rdi+192]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+320]
	mulx r10, rax, QWORD PTR [rdi+328]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+336]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+344]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+200]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+320]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+328]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+336]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+344]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+208]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+336]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+344]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+216]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+336]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+344]
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
	mulx rcx, rax, r12
	shl r11, 1
	sbb rbp, rbp
	shr r11, 1
	and rbp, 19
	add rax, rbp
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov r8, QWORD PTR [rdi+96]
	add r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+104]
	adc r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+112]
	adc r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+120]
	adc r11, QWORD PTR [rdi+88]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov rdx, QWORD PTR [rdi+224]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+352]
	mulx r10, rax, QWORD PTR [rdi+360]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+368]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+376]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+352]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+360]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+376]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+352]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+360]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+376]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+248]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+352]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+360]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+376]
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
	mulx rcx, rax, r12
	shl r11, 1
	sbb rbp, rbp
	shr r11, 1
	and rbp, 19
	add rax, rbp
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+160]
	mulx r10, rax, QWORD PTR [rdi+168]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+176]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+184]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+184]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+184]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+184]
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
	mulx rcx, rax, r12
	shl r11, 1
	sbb rbp, rbp
	shr r11, 1
	and rbp, 19
	add rax, rbp
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov rdx, QWORD PTR [rdi+288]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+128]
	mulx r10, rax, QWORD PTR [rdi+136]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+144]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+152]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+152]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+304]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+152]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+312]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+152]
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
	mulx rcx, rax, r12
	shl r11, 1
	sbb rbp, rbp
	shr r11, 1
	and rbp, 19
	add rax, rbp
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+416], r8
	mov QWORD PTR [rdi+424], r9
	mov QWORD PTR [rdi+432], r10
	mov QWORD PTR [rdi+440], r11
	mov r8, QWORD PTR [rdi+352]
	sub r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+360]
	sbb r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+368]
	sbb r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+376]
	sbb r11, QWORD PTR [rdi+344]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+448], r8
	mov QWORD PTR [rdi+456], r9
	mov QWORD PTR [rdi+464], r10
	mov QWORD PTR [rdi+472], r11
	mov r8, QWORD PTR [rdi+416]
	sub r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+424]
	sbb r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+432]
	sbb r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+440]
	sbb r11, QWORD PTR [rdi+408]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+480], r8
	mov QWORD PTR [rdi+488], r9
	mov QWORD PTR [rdi+496], r10
	mov QWORD PTR [rdi+504], r11
	mov r8, QWORD PTR [rdi+416]
	add r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+424]
	adc r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+432]
	adc r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+440]
	adc r11, QWORD PTR [rdi+408]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+352]
	add r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+360]
	adc r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+368]
	adc r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+376]
	adc r11, QWORD PTR [rdi+344]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+480]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+448]
	mulx r10, rax, QWORD PTR [rdi+456]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+464]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+472]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+488]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+448]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+456]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+464]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+472]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+496]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+448]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+456]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+464]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+472]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+504]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+448]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+456]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+464]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+472]
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
	mulx rcx, rax, r12
	shl r11, 1
	sbb rbp, rbp
	shr r11, 1
	and rbp, 19
	add rax, rbp
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+512]
	mulx r10, rax, QWORD PTR [rdi+520]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+528]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+536]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
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
	mulx r13, rax, QWORD PTR [rdi+536]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
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
	mulx r14, rax, QWORD PTR [rdi+536]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
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
	mulx r15, rax, QWORD PTR [rdi+536]
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
	mulx rcx, rax, r12
	shl r11, 1
	sbb rbp, rbp
	shr r11, 1
	and rbp, 19
	add rax, rbp
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+480]
	mulx r10, rax, QWORD PTR [rdi+488]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+496]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+504]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+480]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+488]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+496]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+504]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+480]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+488]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+496]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+504]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+480]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+488]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+496]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+504]
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
	mulx rcx, rax, r12
	shl r11, 1
	sbb rbp, rbp
	shr r11, 1
	and rbp, 19
	add rax, rbp
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	movq rbp, xmm0
	movq r12, xmm1
	movq r13, xmm2
	movq r14, xmm3
	movq r15, xmm4
	ret
	.p2align 6
