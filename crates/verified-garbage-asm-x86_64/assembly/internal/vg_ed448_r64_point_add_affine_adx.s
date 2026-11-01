// The functions of `src/internal/vg_ed448_r64_point_add_affine_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
