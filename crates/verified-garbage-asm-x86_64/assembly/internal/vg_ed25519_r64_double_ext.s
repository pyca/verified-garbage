// The functions of `src/internal/vg_ed25519_r64_double_ext.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_r64_double_ext:
	movq xmm0, rbp
	movq xmm1, r12
	movq xmm2, r13
	movq xmm3, r14
	movq xmm4, r15
	mov rcx, QWORD PTR [rdi+72]
	mov rbp, QWORD PTR [rdi+80]
	mov r15, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+64]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+64]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+72]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+72]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+80]
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
	mov rax, QWORD PTR [rdi+64]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+80]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+88]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov rcx, QWORD PTR [rdi+136]
	mov rbp, QWORD PTR [rdi+144]
	mov r15, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+128]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+128]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+136]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+136]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+144]
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
	mov rax, QWORD PTR [rdi+128]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+144]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+152]
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
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov r14, QWORD PTR [rdi+96]
	mov r15, QWORD PTR [rdi+104]
	mov rcx, QWORD PTR [rdi+112]
	mov rbp, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+64]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+64]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+72]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+72]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+80]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+64]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+80]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+88]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+72]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+88]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+80]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+88]
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
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
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
	mov r8, QWORD PTR [rdi+448]
	sub r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+456]
	sbb r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+464]
	sbb r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+472]
	sbb r11, QWORD PTR [rdi+408]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+480], r8
	mov QWORD PTR [rdi+488], r9
	mov QWORD PTR [rdi+496], r10
	mov QWORD PTR [rdi+504], r11
	mov r8, QWORD PTR [rdi+448]
	sub r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+456]
	sbb r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+464]
	sbb r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+472]
	sbb r11, QWORD PTR [rdi+376]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+512]
	sub r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+520]
	sbb r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+528]
	sbb r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+536]
	sbb r11, QWORD PTR [rdi+376]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r14, QWORD PTR [rdi+480]
	mov r15, QWORD PTR [rdi+488]
	mov rcx, QWORD PTR [rdi+496]
	mov rbp, QWORD PTR [rdi+504]
	mov rax, QWORD PTR [rdi+416]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+416]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+424]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+416]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+424]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+432]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+416]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+424]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+432]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+440]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+424]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+432]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+440]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+432]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+440]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+440]
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
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov r14, QWORD PTR [rdi+512]
	mov r15, QWORD PTR [rdi+520]
	mov rcx, QWORD PTR [rdi+528]
	mov rbp, QWORD PTR [rdi+536]
	mov rax, QWORD PTR [rdi+448]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+448]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+456]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+456]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+464]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+448]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+464]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+472]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+456]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+472]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+464]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+472]
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
	mov r14, QWORD PTR [rdi+448]
	mov r15, QWORD PTR [rdi+456]
	mov rcx, QWORD PTR [rdi+464]
	mov rbp, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+480]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+480]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+488]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+488]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+496]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+480]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+496]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+504]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+488]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+504]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+496]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+504]
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
	mov r14, QWORD PTR [rdi+512]
	mov r15, QWORD PTR [rdi+520]
	mov rcx, QWORD PTR [rdi+528]
	mov rbp, QWORD PTR [rdi+536]
	mov rax, QWORD PTR [rdi+416]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+416]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+424]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+416]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+424]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+432]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+416]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+424]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+432]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+440]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+424]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+432]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+440]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+432]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+440]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+440]
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
	movq rbp, xmm0
	movq r12, xmm1
	movq r13, xmm2
	movq r14, xmm3
	movq r15, xmm4
	ret
	.p2align 6
