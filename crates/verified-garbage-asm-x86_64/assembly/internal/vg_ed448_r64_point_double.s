// The functions of `src/internal/vg_ed448_r64_point_double.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_r64_point_double:
	movq xmm0, rbp
	movq xmm1, r12
	movq xmm2, r13
	movq xmm3, r14
	movq xmm4, r15
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	adc r12, QWORD PTR [rdi+160]
	adc r13, QWORD PTR [rdi+168]
	adc r14, QWORD PTR [rdi+176]
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
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
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
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	mov r14, QWORD PTR [rdi+112]
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
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
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
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov QWORD PTR [rdi+992], r12
	mov QWORD PTR [rdi+1000], r13
	mov QWORD PTR [rdi+1008], r14
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12, QWORD PTR [rdi+928]
	mov r13, QWORD PTR [rdi+936]
	mov r14, QWORD PTR [rdi+944]
	add r8, QWORD PTR [rdi+960]
	adc r9, QWORD PTR [rdi+968]
	adc r10, QWORD PTR [rdi+976]
	adc r11, QWORD PTR [rdi+984]
	adc r12, QWORD PTR [rdi+992]
	adc r13, QWORD PTR [rdi+1000]
	adc r14, QWORD PTR [rdi+1008]
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
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
	mov QWORD PTR [rdi+1072], r14
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
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov QWORD PTR [rdi+1120], r12
	mov QWORD PTR [rdi+1128], r13
	mov QWORD PTR [rdi+1136], r14
	mov r8, QWORD PTR [rdi+1088]
	mov r9, QWORD PTR [rdi+1096]
	mov r10, QWORD PTR [rdi+1104]
	mov r11, QWORD PTR [rdi+1112]
	mov r12, QWORD PTR [rdi+1120]
	mov r13, QWORD PTR [rdi+1128]
	mov r14, QWORD PTR [rdi+1136]
	add r8, QWORD PTR [rdi+1088]
	adc r9, QWORD PTR [rdi+1096]
	adc r10, QWORD PTR [rdi+1104]
	adc r11, QWORD PTR [rdi+1112]
	adc r12, QWORD PTR [rdi+1120]
	adc r13, QWORD PTR [rdi+1128]
	adc r14, QWORD PTR [rdi+1136]
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
	mov QWORD PTR [rdi+1152], r8
	mov QWORD PTR [rdi+1160], r9
	mov QWORD PTR [rdi+1168], r10
	mov QWORD PTR [rdi+1176], r11
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	mov r14, QWORD PTR [rdi+1072]
	sub r8, QWORD PTR [rdi+1152]
	sbb r9, QWORD PTR [rdi+1160]
	sbb r10, QWORD PTR [rdi+1168]
	sbb r11, QWORD PTR [rdi+1176]
	sbb r12, QWORD PTR [rdi+1184]
	sbb r13, QWORD PTR [rdi+1192]
	sbb r14, QWORD PTR [rdi+1200]
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
	mov QWORD PTR [rdi+1152], r8
	mov QWORD PTR [rdi+1160], r9
	mov QWORD PTR [rdi+1168], r10
	mov QWORD PTR [rdi+1176], r11
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14, QWORD PTR [rdi+880]
	sub r8, QWORD PTR [rdi+1024]
	sbb r9, QWORD PTR [rdi+1032]
	sbb r10, QWORD PTR [rdi+1040]
	sbb r11, QWORD PTR [rdi+1048]
	sbb r12, QWORD PTR [rdi+1056]
	sbb r13, QWORD PTR [rdi+1064]
	sbb r14, QWORD PTR [rdi+1072]
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
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov QWORD PTR [rdi+1264], r14
	mov r8, QWORD PTR [rdi+1152]
	mov r9, QWORD PTR [rdi+1160]
	mov r10, QWORD PTR [rdi+1168]
	mov r11, QWORD PTR [rdi+1176]
	mov r12, QWORD PTR [rdi+1184]
	mov r13, QWORD PTR [rdi+1192]
	mov r14, QWORD PTR [rdi+1200]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1216]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1224]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1216]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1224]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1232]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1224]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1232]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1240]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1216]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1224]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1232]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1240]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1248]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1216]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1224]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1232]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1240]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1248]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1256]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1224]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1232]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1240]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1248]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1256]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1224]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1232]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1240]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1248]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1256]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1264]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1232]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1240]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1248]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1256]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1264]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1240]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1248]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1256]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1248]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1256]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1264]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1256]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1264]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
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
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12, QWORD PTR [rdi+928]
	mov r13, QWORD PTR [rdi+936]
	mov r14, QWORD PTR [rdi+944]
	sub r8, QWORD PTR [rdi+960]
	sbb r9, QWORD PTR [rdi+968]
	sbb r10, QWORD PTR [rdi+976]
	sbb r11, QWORD PTR [rdi+984]
	sbb r12, QWORD PTR [rdi+992]
	sbb r13, QWORD PTR [rdi+1000]
	sbb r14, QWORD PTR [rdi+1008]
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
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov QWORD PTR [rdi+1312], r12
	mov QWORD PTR [rdi+1320], r13
	mov QWORD PTR [rdi+1328], r14
	mov r8, QWORD PTR [rdi+1280]
	mov r9, QWORD PTR [rdi+1288]
	mov r10, QWORD PTR [rdi+1296]
	mov r11, QWORD PTR [rdi+1304]
	mov r12, QWORD PTR [rdi+1312]
	mov r13, QWORD PTR [rdi+1320]
	mov r14, QWORD PTR [rdi+1328]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1072]
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
	mov r8, QWORD PTR [rdi+1152]
	mov r9, QWORD PTR [rdi+1160]
	mov r10, QWORD PTR [rdi+1168]
	mov r11, QWORD PTR [rdi+1176]
	mov r12, QWORD PTR [rdi+1184]
	mov r13, QWORD PTR [rdi+1192]
	mov r14, QWORD PTR [rdi+1200]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1032]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1040]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1048]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1056]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1064]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1072]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1072]
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
	movq rbp, xmm0
	movq r12, xmm1
	movq r13, xmm2
	movq r14, xmm3
	movq r15, xmm4
	ret
	.p2align 6
