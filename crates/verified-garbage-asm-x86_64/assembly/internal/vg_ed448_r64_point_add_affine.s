// The functions of `src/internal/vg_ed448_r64_point_add_affine.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_r64_point_add_affine:
	movq xmm0, rbp
	movq xmm1, r12
	movq xmm2, r13
	movq xmm3, r14
	movq xmm4, r15
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
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov r8, QWORD PTR [rdi+576]
	mov r9, QWORD PTR [rdi+584]
	mov r10, QWORD PTR [rdi+592]
	mov r11, QWORD PTR [rdi+600]
	mov r12, QWORD PTR [rdi+608]
	mov r13, QWORD PTR [rdi+616]
	mov r14, QWORD PTR [rdi+624]
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
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov QWORD PTR [rdi+992], r12
	mov QWORD PTR [rdi+1000], r13
	mov QWORD PTR [rdi+1008], r14
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	mov r12, QWORD PTR [rdi+672]
	mov r13, QWORD PTR [rdi+680]
	mov r14, QWORD PTR [rdi+688]
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
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
	mov QWORD PTR [rdi+1072], r14
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	mov r12, QWORD PTR [rdi+992]
	mov r13, QWORD PTR [rdi+1000]
	mov r14, QWORD PTR [rdi+1008]
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
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov QWORD PTR [rdi+1120], r12
	mov QWORD PTR [rdi+1128], r13
	mov QWORD PTR [rdi+1136], r14
	mov ecx, 39081
	mov ebp, 0
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
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
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov QWORD PTR [rdi+1120], r12
	mov QWORD PTR [rdi+1128], r13
	mov QWORD PTR [rdi+1136], r14
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	mov r14, QWORD PTR [rdi+1072]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1088]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1088]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1096]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1088]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1096]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1104]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1088]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1096]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1104]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1112]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1088]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1096]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1104]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1112]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1120]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1088]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1096]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1104]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1112]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1120]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1128]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1088]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1096]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1104]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1112]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1128]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1136]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1096]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1104]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1112]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1120]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1128]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1136]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1104]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1112]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1120]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1128]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1136]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1112]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1128]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1136]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1120]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1128]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1136]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1128]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1136]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1136]
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
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12, QWORD PTR [rdi+928]
	mov r13, QWORD PTR [rdi+936]
	mov r14, QWORD PTR [rdi+944]
	sub r8, QWORD PTR [rdi+1088]
	sbb r9, QWORD PTR [rdi+1096]
	sbb r10, QWORD PTR [rdi+1104]
	sbb r11, QWORD PTR [rdi+1112]
	sbb r12, QWORD PTR [rdi+1120]
	sbb r13, QWORD PTR [rdi+1128]
	sbb r14, QWORD PTR [rdi+1136]
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
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12, QWORD PTR [rdi+928]
	mov r13, QWORD PTR [rdi+936]
	mov r14, QWORD PTR [rdi+944]
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
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov QWORD PTR [rdi+1264], r14
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
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov QWORD PTR [rdi+1312], r12
	mov QWORD PTR [rdi+1320], r13
	mov QWORD PTR [rdi+1328], r14
	mov r8, QWORD PTR [rdi+576]
	mov r9, QWORD PTR [rdi+584]
	mov r10, QWORD PTR [rdi+592]
	mov r11, QWORD PTR [rdi+600]
	mov r12, QWORD PTR [rdi+608]
	mov r13, QWORD PTR [rdi+616]
	mov r14, QWORD PTR [rdi+624]
	add r8, QWORD PTR [rdi+640]
	adc r9, QWORD PTR [rdi+648]
	adc r10, QWORD PTR [rdi+656]
	adc r11, QWORD PTR [rdi+664]
	adc r12, QWORD PTR [rdi+672]
	adc r13, QWORD PTR [rdi+680]
	adc r14, QWORD PTR [rdi+688]
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
	mov rax, QWORD PTR [rdi+1280]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1280]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1288]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1280]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1288]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1296]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1280]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1288]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1296]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1304]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1280]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1288]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1296]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1304]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1312]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1280]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1288]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1296]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1304]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1312]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1320]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1280]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1288]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1296]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1304]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1312]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1320]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1328]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1288]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1296]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1304]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1312]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1320]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1328]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1296]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1304]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1312]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1320]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1328]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1304]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1312]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1320]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1328]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1312]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1320]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1328]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1320]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1328]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1328]
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
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov QWORD PTR [rdi+1312], r12
	mov QWORD PTR [rdi+1320], r13
	mov QWORD PTR [rdi+1328], r14
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
	mov rax, QWORD PTR [rdi+192]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+192]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+200]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+192]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+200]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+208]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+200]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+208]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+216]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+192]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+200]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+208]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+224]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+192]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+200]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+208]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+216]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+224]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+232]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+200]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+208]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+216]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+224]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+232]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+240]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+200]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+208]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+224]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+232]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+240]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+208]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+216]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+224]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+232]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+240]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+216]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+224]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+232]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+240]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+224]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+232]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+240]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+232]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+240]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+240]
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
	mov r8, QWORD PTR [rdi+1280]
	mov r9, QWORD PTR [rdi+1288]
	mov r10, QWORD PTR [rdi+1296]
	mov r11, QWORD PTR [rdi+1304]
	mov r12, QWORD PTR [rdi+1312]
	mov r13, QWORD PTR [rdi+1320]
	mov r14, QWORD PTR [rdi+1328]
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
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14, QWORD PTR [rdi+1264]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+192]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+200]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+192]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+200]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+208]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+200]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+208]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+216]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+192]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+200]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+208]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+224]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+192]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+200]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+208]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+216]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+224]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+232]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+200]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+208]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+216]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+224]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+232]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+240]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+200]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+208]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+224]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+232]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+240]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+208]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+216]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+224]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+232]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+240]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+216]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+224]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+232]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+240]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+224]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+232]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+240]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+232]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+240]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+240]
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
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	mov r14, QWORD PTR [rdi+1072]
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
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14, QWORD PTR [rdi+1264]
	mov r15d, 0
	mov ecx, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1152]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1536], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1152]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1160]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1544], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1152]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1160]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1168]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1552], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1152]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1160]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1168]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1176]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1560], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1152]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1160]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1168]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1176]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1184]
	mul r8
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1568], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1152]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1160]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1168]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1176]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1184]
	mul r9
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1192]
	mul r8
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1576], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1152]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1160]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1168]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1176]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul r10
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1192]
	mul r9
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1200]
	mul r8
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1584], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1160]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1168]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1176]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1184]
	mul r11
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1192]
	mul r10
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1200]
	mul r9
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1592], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1168]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1176]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1184]
	mul r12
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1192]
	mul r11
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1200]
	mul r10
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1600], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1176]
	mul r14
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul r13
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1192]
	mul r12
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1200]
	mul r11
	add r15, rax
	adc rcx, rdx
	adc rbp, 0
	mov QWORD PTR [rdi+1608], r15
	mov r15d, 0
	mov rax, QWORD PTR [rdi+1184]
	mul r14
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1192]
	mul r13
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+1200]
	mul r12
	add rcx, rax
	adc rbp, rdx
	adc r15, 0
	mov QWORD PTR [rdi+1616], rcx
	mov ecx, 0
	mov rax, QWORD PTR [rdi+1192]
	mul r14
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov rax, QWORD PTR [rdi+1200]
	mul r13
	add rbp, rax
	adc r15, rdx
	adc rcx, 0
	mov QWORD PTR [rdi+1624], rbp
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1200]
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
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov QWORD PTR [rdi+416], r12
	mov QWORD PTR [rdi+424], r13
	mov QWORD PTR [rdi+432], r14
	movq rbp, xmm0
	movq r12, xmm1
	movq r13, xmm2
	movq r14, xmm3
	movq r15, xmm4
	ret
	.p2align 6
