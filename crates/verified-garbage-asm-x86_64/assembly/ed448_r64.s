// The functions of `src/ed448_r64.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_r64_point_double_adx:
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
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+832]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+840]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+848]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+856]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+864]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+872]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+856]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+864]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+872]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+880]
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
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+64]
	mov r15d, 0
	xor ebp, ebp
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
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+72]
	mov r8d, 0
	xor ebp, ebp
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
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+80]
	mov r9d, 0
	xor ebp, ebp
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
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+88]
	mov r10d, 0
	xor ebp, ebp
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
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+96]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+104]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+72]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+80]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+88]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+96]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+104]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+112]
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
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+128]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+136]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+144]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+152]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+160]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+168]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+128]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+136]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+144]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+152]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+160]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+168]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+176]
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
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+192]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+200]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+208]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+216]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+224]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+232]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+192]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+200]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+208]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+216]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+224]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+232]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+240]
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1152]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1160]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1168]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1176]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1184]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1192]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1200]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1264]
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1280]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1288]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1296]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1304]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1312]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1320]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1328]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
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
	mov rdx, QWORD PTR [rdi+1152]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1160]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1168]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1176]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1184]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1192]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1200]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1024]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1032]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1040]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1048]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1056]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1064]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1072]
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
	movq rbp, xmm0
	movq r12, xmm1
	movq r13, xmm2
	movq r14, xmm3
	movq r15, xmm4
	ret
	.p2align 6

vg_ed448_r64_point_add_affine_adx:
	movq xmm0, rbp
	movq xmm1, r12
	movq xmm2, r13
	movq xmm3, r14
	movq xmm4, r15
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+192]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+200]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+208]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+216]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+224]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+232]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+192]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+200]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+208]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+216]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+224]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+232]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+240]
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
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+576]
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
	mov rdx, QWORD PTR [rdi+584]
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
	mov rdx, QWORD PTR [rdi+592]
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
	mov rdx, QWORD PTR [rdi+600]
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
	mov rdx, QWORD PTR [rdi+608]
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
	mov rdx, QWORD PTR [rdi+616]
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
	mov rdx, QWORD PTR [rdi+624]
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
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov QWORD PTR [rdi+992], r12
	mov QWORD PTR [rdi+1000], r13
	mov QWORD PTR [rdi+1008], r14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+640]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+648]
	mov r8d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+656]
	mov r9d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+664]
	mov r10d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+672]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+680]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+688]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1024]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1088]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1096]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1104]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1112]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1032]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1088]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1096]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1104]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1112]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1040]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1088]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1096]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1112]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1048]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1088]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1096]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1104]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1112]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1056]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1088]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1096]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1104]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1112]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1064]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1088]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1096]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1104]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1112]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1072]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1088]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1096]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1104]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1112]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1344]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1352]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1360]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1368]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1376]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1384]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1392]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
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
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov QWORD PTR [rdi+1312], r12
	mov QWORD PTR [rdi+1320], r13
	mov QWORD PTR [rdi+1328], r14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1152]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1160]
	mov r8d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1168]
	mov r9d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1176]
	mov r10d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1184]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1192]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1200]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1280]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1288]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1296]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1304]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1312]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1320]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1328]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
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
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1216]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1224]
	mov r8d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1232]
	mov r9d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1240]
	mov r10d, 0
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
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1248]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1256]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1264]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+240]
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1280]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1288]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1296]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1304]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1312]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1320]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1328]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
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
	mov rdx, QWORD PTR [rdi+1216]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1224]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1232]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1240]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1248]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1256]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1264]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
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
