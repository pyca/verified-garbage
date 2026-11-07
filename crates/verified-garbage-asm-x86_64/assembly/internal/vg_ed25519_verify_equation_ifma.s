// The functions of `src/internal/vg_ed25519_verify_equation_ifma.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_verify_equation_ifma:
	mov rax, rdx
	mov rdx, rcx
	mov QWORD PTR [rdx], rbx
	mov QWORD PTR [rdx+8], rbp
	mov QWORD PTR [rdx+16], r12
	mov QWORD PTR [rdx+24], r13
	mov QWORD PTR [rdx+32], r14
	mov QWORD PTR [rdx+40], r15
	mov QWORD PTR [rdx+7936], rdi
	mov QWORD PTR [rdx+7944], rsi
	mov QWORD PTR [rdx+7952], rax
	mov rdi, rdx
	lea rax, {VG_ED25519_VERIFY_BASE}
	mov QWORD PTR [rdi+7960], rax
	mov rdx, QWORD PTR [rdi+7944]
	add rdx, 32
	mov r8, QWORD PTR [rdx]
	mov r9, QWORD PTR [rdx+8]
	mov r10, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	mov r12, r8
	mov r13, r9
	mov r14, r10
	mov r15, r11
	movabs rcx, 6346243789798364141
	sub r8, rcx
	movabs rcx, 1503914060200516822
	sbb r9, rcx
	sbb r10, 0
	movabs rcx, 1152921504606846976
	sbb r11, rcx
	jb 20f
	mov eax, 0
	jmp 21f
20:
	call {vg_ed25519_decode_powers_adx}
	mov rdx, QWORD PTR [rdi+7936]
	call {vg_ed25519_point_decode_adx}
	test rax, rax
	jne 22f
	mov eax, 0
	jmp 23f
22:
	movabs rbx, 0
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 7424
	add rax, rcx
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov r8, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+120]
	mov QWORD PTR [rax+32], r8
	mov QWORD PTR [rax+40], r9
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r11
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rax+64], r8
	mov QWORD PTR [rax+72], r9
	mov QWORD PTR [rax+80], r10
	mov QWORD PTR [rax+88], r11
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	mov QWORD PTR [rax+96], r8
	mov QWORD PTR [rax+104], r9
	mov QWORD PTR [rax+112], r10
	mov QWORD PTR [rax+120], r11
	mov rax, rdi
	mov r8, QWORD PTR [rax+7680]
	mov r9, QWORD PTR [rax+7688]
	mov r10, QWORD PTR [rax+7696]
	mov r11, QWORD PTR [rax+7704]
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+7944]
	call {vg_ed25519_point_decode_adx}
	test rax, rax
	jne 24f
	mov eax, 0
	jmp 25f
24:
	movabs rbx, 0
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 7552
	add rax, rcx
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov r8, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+120]
	mov QWORD PTR [rax+32], r8
	mov QWORD PTR [rax+40], r9
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r11
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rax+64], r8
	mov QWORD PTR [rax+72], r9
	mov QWORD PTR [rax+80], r10
	mov QWORD PTR [rax+88], r11
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	mov QWORD PTR [rax+96], r8
	mov QWORD PTR [rax+104], r9
	mov QWORD PTR [rax+112], r10
	mov QWORD PTR [rax+120], r11
	movabs r8, 8496970652267935907
	movabs r9, 31536524315187371
	movabs r10, -8302596497594521448
	movabs r11, 5909686906226998899
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	movabs rax, 7424
	add rax, rdi
	mov r8, QWORD PTR [rax]
	mov r9, QWORD PTR [rax+8]
	mov r10, QWORD PTR [rax+16]
	mov r11, QWORD PTR [rax+24]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov r8, QWORD PTR [rax+32]
	mov r9, QWORD PTR [rax+40]
	mov r10, QWORD PTR [rax+48]
	mov r11, QWORD PTR [rax+56]
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r8, QWORD PTR [rax+64]
	mov r9, QWORD PTR [rax+72]
	mov r10, QWORD PTR [rax+80]
	mov r11, QWORD PTR [rax+88]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov r8, QWORD PTR [rax+96]
	mov r9, QWORD PTR [rax+104]
	mov r10, QWORD PTR [rax+112]
	mov r11, QWORD PTR [rax+120]
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	call {vg_ed25519_r64_double_ext_adx}
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
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+160]
	mulx r10, rax, QWORD PTR [rdi+168]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+176]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+184]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
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
	mov rdx, QWORD PTR [rdi+592]
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
	mov rdx, QWORD PTR [rdi+600]
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
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	mulx rcx, rax, r12
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov r8, QWORD PTR [rdi+128]
	add r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	adc r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	adc r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	adc r11, QWORD PTR [rdi+152]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+416], r8
	mov QWORD PTR [rdi+424], r9
	mov QWORD PTR [rdi+432], r10
	mov QWORD PTR [rdi+440], r11
	movabs rax, 3216
	add rax, rdi
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+376]
	mov QWORD PTR [rax+32], r8
	mov QWORD PTR [rax+40], r9
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r11
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov QWORD PTR [rax+64], r8
	mov QWORD PTR [rax+72], r9
	mov QWORD PTR [rax+80], r10
	mov QWORD PTR [rax+88], r11
	mov r8, QWORD PTR [rdi+416]
	mov r9, QWORD PTR [rdi+424]
	mov r10, QWORD PTR [rdi+432]
	mov r11, QWORD PTR [rdi+440]
	mov QWORD PTR [rax+96], r8
	mov QWORD PTR [rax+104], r9
	mov QWORD PTR [rax+112], r10
	mov QWORD PTR [rax+120], r11
	movabs rax, 7424
	add rax, rdi
	mov r8, QWORD PTR [rax]
	mov r9, QWORD PTR [rax+8]
	mov r10, QWORD PTR [rax+16]
	mov r11, QWORD PTR [rax+24]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov r8, QWORD PTR [rax+32]
	mov r9, QWORD PTR [rax+40]
	mov r10, QWORD PTR [rax+48]
	mov r11, QWORD PTR [rax+56]
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r8, QWORD PTR [rax+64]
	mov r9, QWORD PTR [rax+72]
	mov r10, QWORD PTR [rax+80]
	mov r11, QWORD PTR [rax+88]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov r8, QWORD PTR [rax+96]
	mov r9, QWORD PTR [rax+104]
	mov r10, QWORD PTR [rax+112]
	mov r11, QWORD PTR [rax+120]
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov ebx, 0
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
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+160]
	mulx r10, rax, QWORD PTR [rdi+168]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+176]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+184]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
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
	mov rdx, QWORD PTR [rdi+592]
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
	mov rdx, QWORD PTR [rdi+600]
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
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	mulx rcx, rax, r12
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov r8, QWORD PTR [rdi+128]
	add r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	adc r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	adc r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	adc r11, QWORD PTR [rdi+152]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+416], r8
	mov QWORD PTR [rdi+424], r9
	mov QWORD PTR [rdi+432], r10
	mov QWORD PTR [rdi+440], r11
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5376
	add rax, rcx
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+376]
	mov QWORD PTR [rax+32], r8
	mov QWORD PTR [rax+40], r9
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r11
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov QWORD PTR [rax+64], r8
	mov QWORD PTR [rax+72], r9
	mov QWORD PTR [rax+80], r10
	mov QWORD PTR [rax+88], r11
	mov r8, QWORD PTR [rdi+416]
	mov r9, QWORD PTR [rdi+424]
	mov r10, QWORD PTR [rdi+432]
	mov r11, QWORD PTR [rdi+440]
	mov QWORD PTR [rax+96], r8
	mov QWORD PTR [rax+104], r9
	mov QWORD PTR [rax+112], r10
	mov QWORD PTR [rax+120], r11
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+344]
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
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+344]
	sbb r11, QWORD PTR [rdi+184]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
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
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+160]
	mulx r10, rax, QWORD PTR [rdi+168]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+176]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+184]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
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
	mov rdx, QWORD PTR [rdi+592]
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
	mov rdx, QWORD PTR [rdi+600]
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
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	mulx rcx, rax, r12
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov r8, QWORD PTR [rdi+128]
	add r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	adc r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	adc r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	adc r11, QWORD PTR [rdi+152]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+416], r8
	mov QWORD PTR [rdi+424], r9
	mov QWORD PTR [rdi+432], r10
	mov QWORD PTR [rdi+440], r11
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5504
	add rax, rcx
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+376]
	mov QWORD PTR [rax+32], r8
	mov QWORD PTR [rax+40], r9
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r11
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov QWORD PTR [rax+64], r8
	mov QWORD PTR [rax+72], r9
	mov QWORD PTR [rax+80], r10
	mov QWORD PTR [rax+88], r11
	mov r8, QWORD PTR [rdi+416]
	mov r9, QWORD PTR [rdi+424]
	mov r10, QWORD PTR [rdi+432]
	mov r11, QWORD PTR [rdi+440]
	mov QWORD PTR [rax+96], r8
	mov QWORD PTR [rax+104], r9
	mov QWORD PTR [rax+112], r10
	mov QWORD PTR [rax+120], r11
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+344]
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
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+344]
	sbb r11, QWORD PTR [rdi+184]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov ebx, 2
26:
	movabs rax, 3216
	add rax, rdi
	mov r8, QWORD PTR [rax]
	mov r9, QWORD PTR [rax+8]
	mov r10, QWORD PTR [rax+16]
	mov r11, QWORD PTR [rax+24]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov r8, QWORD PTR [rax+32]
	mov r9, QWORD PTR [rax+40]
	mov r10, QWORD PTR [rax+48]
	mov r11, QWORD PTR [rax+56]
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rax+64]
	mov r9, QWORD PTR [rax+72]
	mov r10, QWORD PTR [rax+80]
	mov r11, QWORD PTR [rax+88]
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov r8, QWORD PTR [rax+96]
	mov r9, QWORD PTR [rax+104]
	mov r10, QWORD PTR [rax+112]
	mov r11, QWORD PTR [rax+120]
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	call {vg_ed25519_r64_add_cached_ext_adx}
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
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+160]
	mulx r10, rax, QWORD PTR [rdi+168]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+176]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+184]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
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
	mov rdx, QWORD PTR [rdi+592]
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
	mov rdx, QWORD PTR [rdi+600]
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
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	mulx rcx, rax, r12
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov r8, QWORD PTR [rdi+128]
	add r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	adc r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	adc r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	adc r11, QWORD PTR [rdi+152]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+416], r8
	mov QWORD PTR [rdi+424], r9
	mov QWORD PTR [rdi+432], r10
	mov QWORD PTR [rdi+440], r11
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5376
	add rax, rcx
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+376]
	mov QWORD PTR [rax+32], r8
	mov QWORD PTR [rax+40], r9
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r11
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov QWORD PTR [rax+64], r8
	mov QWORD PTR [rax+72], r9
	mov QWORD PTR [rax+80], r10
	mov QWORD PTR [rax+88], r11
	mov r8, QWORD PTR [rdi+416]
	mov r9, QWORD PTR [rdi+424]
	mov r10, QWORD PTR [rdi+432]
	mov r11, QWORD PTR [rdi+440]
	mov QWORD PTR [rax+96], r8
	mov QWORD PTR [rax+104], r9
	mov QWORD PTR [rax+112], r10
	mov QWORD PTR [rax+120], r11
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+344]
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
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+344]
	sbb r11, QWORD PTR [rdi+184]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
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
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+160]
	mulx r10, rax, QWORD PTR [rdi+168]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+176]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+184]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
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
	mov rdx, QWORD PTR [rdi+592]
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
	mov rdx, QWORD PTR [rdi+600]
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
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	mulx rcx, rax, r12
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov r8, QWORD PTR [rdi+128]
	add r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	adc r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	adc r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	adc r11, QWORD PTR [rdi+152]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	sbb rax, rax
	and rax, 38
	add r8, rax
	mov QWORD PTR [rdi+416], r8
	mov QWORD PTR [rdi+424], r9
	mov QWORD PTR [rdi+432], r10
	mov QWORD PTR [rdi+440], r11
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5504
	add rax, rcx
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+376]
	mov QWORD PTR [rax+32], r8
	mov QWORD PTR [rax+40], r9
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r11
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov QWORD PTR [rax+64], r8
	mov QWORD PTR [rax+72], r9
	mov QWORD PTR [rax+80], r10
	mov QWORD PTR [rax+88], r11
	mov r8, QWORD PTR [rdi+416]
	mov r9, QWORD PTR [rdi+424]
	mov r10, QWORD PTR [rdi+432]
	mov r11, QWORD PTR [rdi+440]
	mov QWORD PTR [rax+96], r8
	mov QWORD PTR [rax+104], r9
	mov QWORD PTR [rax+112], r10
	mov QWORD PTR [rax+120], r11
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+344]
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
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+344]
	sbb r11, QWORD PTR [rdi+184]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	add rbx, 2
	cmp rbx, 16
	jne 26b
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	movabs rax, 64
	mov QWORD PTR [rdi+56], rax
27:
	mov rbx, QWORD PTR [rdi+56]
	sub rbx, 1
	mov QWORD PTR [rdi+56], rbx
	mov rsi, QWORD PTR [rdi+7952]
	add rsi, 0
	mov rax, QWORD PTR [rdi+56]
	movzx ebx, BYTE PTR [rsi+rax*1]
	test rbx, rbx
	jne 28f
	mov rbx, QWORD PTR [rdi+56]
	cmp rbx, 32
	jmp 29f
28:
	mov rax, QWORD PTR [rdi+56]
	add rax, 1
	mov QWORD PTR [rdi+56], rax
	cmp rax, rax
29:
	jne 27b
	mov eax, 0
	mov QWORD PTR [rdi+2048], rax
	mov QWORD PTR [rdi+2056], rax
	mov QWORD PTR [rdi+2064], rax
	mov QWORD PTR [rdi+2072], rax
	mov QWORD PTR [rdi+2080], rax
	mov QWORD PTR [rdi+2088], rax
	mov QWORD PTR [rdi+2096], rax
	mov QWORD PTR [rdi+2104], rax
	mov QWORD PTR [rdi+2112], rax
	mov QWORD PTR [rdi+2120], rax
	mov QWORD PTR [rdi+2128], rax
	mov QWORD PTR [rdi+2136], rax
	mov QWORD PTR [rdi+2144], rax
	mov QWORD PTR [rdi+2152], rax
	mov QWORD PTR [rdi+2160], rax
	mov QWORD PTR [rdi+2168], rax
	mov QWORD PTR [rdi+2176], rax
	mov QWORD PTR [rdi+2184], rax
	mov QWORD PTR [rdi+2192], rax
	mov QWORD PTR [rdi+2200], rax
	mov QWORD PTR [rdi+2208], rax
	mov QWORD PTR [rdi+2216], rax
	mov QWORD PTR [rdi+2224], rax
	mov QWORD PTR [rdi+2232], rax
	mov QWORD PTR [rdi+2240], rax
	mov QWORD PTR [rdi+2248], rax
	mov QWORD PTR [rdi+2256], rax
	mov QWORD PTR [rdi+2264], rax
	mov QWORD PTR [rdi+2272], rax
	mov QWORD PTR [rdi+2280], rax
	mov QWORD PTR [rdi+2288], rax
	mov QWORD PTR [rdi+2296], rax
	mov QWORD PTR [rdi+2304], rax
	mov QWORD PTR [rdi+2312], rax
	mov QWORD PTR [rdi+2320], rax
	mov QWORD PTR [rdi+2328], rax
	mov QWORD PTR [rdi+2336], rax
	mov QWORD PTR [rdi+2344], rax
	mov QWORD PTR [rdi+2352], rax
	mov QWORD PTR [rdi+2360], rax
	mov QWORD PTR [rdi+2368], rax
	mov QWORD PTR [rdi+2376], rax
	mov QWORD PTR [rdi+2384], rax
	mov QWORD PTR [rdi+2392], rax
	mov QWORD PTR [rdi+2400], rax
	mov QWORD PTR [rdi+2408], rax
	mov QWORD PTR [rdi+2416], rax
	mov QWORD PTR [rdi+2424], rax
	mov QWORD PTR [rdi+2432], rax
	mov QWORD PTR [rdi+2440], rax
	mov QWORD PTR [rdi+2448], rax
	mov QWORD PTR [rdi+2456], rax
	mov QWORD PTR [rdi+2464], rax
	mov QWORD PTR [rdi+2472], rax
	mov QWORD PTR [rdi+2480], rax
	mov QWORD PTR [rdi+2488], rax
	mov QWORD PTR [rdi+2496], rax
	mov QWORD PTR [rdi+2504], rax
	mov QWORD PTR [rdi+2512], rax
	mov QWORD PTR [rdi+2520], rax
	mov QWORD PTR [rdi+2528], rax
	mov QWORD PTR [rdi+2536], rax
	mov QWORD PTR [rdi+2544], rax
	mov QWORD PTR [rdi+2552], rax
	mov QWORD PTR [rdi+2560], rax
	mov QWORD PTR [rdi+2568], rax
	mov QWORD PTR [rdi+2576], rax
	mov QWORD PTR [rdi+2584], rax
	mov QWORD PTR [rdi+2592], rax
	mov QWORD PTR [rdi+2600], rax
	mov QWORD PTR [rdi+2608], rax
	mov QWORD PTR [rdi+2616], rax
	mov QWORD PTR [rdi+2624], rax
	mov QWORD PTR [rdi+2632], rax
	mov QWORD PTR [rdi+2640], rax
	mov QWORD PTR [rdi+2648], rax
	mov QWORD PTR [rdi+2656], rax
	mov QWORD PTR [rdi+2664], rax
	mov QWORD PTR [rdi+2672], rax
	mov QWORD PTR [rdi+2680], rax
	mov QWORD PTR [rdi+2688], rax
	mov QWORD PTR [rdi+2696], rax
	mov QWORD PTR [rdi+2704], rax
	mov QWORD PTR [rdi+2712], rax
	mov QWORD PTR [rdi+2720], rax
	mov QWORD PTR [rdi+2728], rax
	mov QWORD PTR [rdi+2736], rax
	mov QWORD PTR [rdi+2744], rax
	mov QWORD PTR [rdi+2752], rax
	mov QWORD PTR [rdi+2760], rax
	mov QWORD PTR [rdi+2768], rax
	mov QWORD PTR [rdi+2776], rax
	mov QWORD PTR [rdi+2784], rax
	mov QWORD PTR [rdi+2792], rax
	mov QWORD PTR [rdi+2800], rax
	mov QWORD PTR [rdi+2808], rax
	mov QWORD PTR [rdi+2816], rax
	mov QWORD PTR [rdi+2824], rax
	mov QWORD PTR [rdi+2832], rax
	mov QWORD PTR [rdi+2840], rax
	mov QWORD PTR [rdi+2848], rax
	mov QWORD PTR [rdi+2856], rax
	mov QWORD PTR [rdi+2864], rax
	mov QWORD PTR [rdi+2872], rax
	mov QWORD PTR [rdi+2880], rax
	mov QWORD PTR [rdi+2888], rax
	mov QWORD PTR [rdi+2896], rax
	mov QWORD PTR [rdi+2904], rax
	mov QWORD PTR [rdi+2912], rax
	mov QWORD PTR [rdi+2920], rax
	mov QWORD PTR [rdi+2928], rax
	mov QWORD PTR [rdi+2936], rax
	mov QWORD PTR [rdi+2944], rax
	mov QWORD PTR [rdi+2952], rax
	mov QWORD PTR [rdi+2960], rax
	mov QWORD PTR [rdi+2968], rax
	mov QWORD PTR [rdi+2976], rax
	mov QWORD PTR [rdi+2984], rax
	mov QWORD PTR [rdi+2992], rax
	mov QWORD PTR [rdi+3000], rax
	mov QWORD PTR [rdi+3008], rax
	mov QWORD PTR [rdi+3016], rax
	mov QWORD PTR [rdi+3024], rax
	mov QWORD PTR [rdi+3032], rax
	mov QWORD PTR [rdi+3040], rax
	mov QWORD PTR [rdi+3048], rax
	mov QWORD PTR [rdi+3056], rax
	mov QWORD PTR [rdi+3064], rax
	mov QWORD PTR [rdi+3072], rax
	mov QWORD PTR [rdi+3080], rax
	mov QWORD PTR [rdi+3088], rax
	mov QWORD PTR [rdi+3096], rax
	mov rsi, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+3160], rax
	mov rsi, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+3200], rax
	mov eax, 0
	mov QWORD PTR [rdi+3168], rax
	mov QWORD PTR [rdi+3208], rax
	mov esi, 0
	mov r8d, 0
210:
	mov rax, rsi
	shr rax, 3
	mov rbx, QWORD PTR [rdi+rax*1+3104]
	mov rcx, rsi
	and rcx, 7
	mov rdx, rbx
	shr rdx, 4
	test rcx, 4
	cmovne rbx, rdx
	mov rdx, rbx
	shr rdx, 2
	test rcx, 2
	cmovne rbx, rdx
	mov rdx, rbx
	shr rdx, 1
	test rcx, 1
	cmovne rbx, rdx
	mov rax, rbx
	and rax, 1
	cmp rax, r8
	je 211f
	and rbx, 31
	add rbx, r8
	cmp rbx, 16
	jb 213f
	mov eax, 33
	sub rax, rbx
	mov rbx, rax
	mov r8d, 1
	jmp 214f
213:
	mov r8d, 0
214:
	mov rax, rsi
	add rax, rax
	mov BYTE PTR [rdi+rax*1+2048], bl
	add rsi, 5
	jmp 212f
211:
	add rsi, 1
212:
	mov rax, QWORD PTR [rdi+56]
	shl rax, 3
	cmp rsi, rax
	jb 210b
	test r8, r8
	jne 215f
	jmp 216f
215:
	mov rax, rsi
	add rax, rax
	mov ebx, 1
	mov BYTE PTR [rdi+rax*1+2048], bl
216:
	mov esi, 0
	mov r8d, 0
217:
	mov rax, rsi
	shr rax, 3
	mov rbx, QWORD PTR [rdi+rax*1+3176]
	mov rcx, rsi
	and rcx, 7
	mov rdx, rbx
	shr rdx, 4
	test rcx, 4
	cmovne rbx, rdx
	mov rdx, rbx
	shr rdx, 2
	test rcx, 2
	cmovne rbx, rdx
	mov rdx, rbx
	shr rdx, 1
	test rcx, 1
	cmovne rbx, rdx
	mov rax, rbx
	and rax, 1
	cmp rax, r8
	je 218f
	and rbx, 255
	add rbx, r8
	cmp rbx, 128
	jb 220f
	mov eax, 257
	sub rax, rbx
	mov rbx, rax
	mov r8d, 1
	jmp 221f
220:
	mov r8d, 0
221:
	mov rax, rsi
	add rax, rax
	mov BYTE PTR [rdi+rax*1+2049], bl
	add rsi, 8
	jmp 219f
218:
	add rsi, 1
219:
	cmp rsi, 256
	jb 217b
	test r8, r8
	jne 222f
	jmp 223f
222:
	mov rax, rsi
	add rax, rax
	mov ebx, 1
	mov BYTE PTR [rdi+rax*1+2049], bl
223:
	mov rax, QWORD PTR [rdi+56]
	shl rax, 3
	add rax, 9
	mov QWORD PTR [rdi+56], rax
	movabs rax, 2251799813685247
	mov ecx, 19
	movabs rdx, 4611686018427348992
	movabs rbp, 4611686018427385856
	mov r8d, 8191
	mov r9d, 67108863
	movabs r10, 549755813887
	mov r11d, 1
	mov r12d, 121665
	vmovq xmm9, rax
	vpbroadcastq ymm9, xmm9
	vmovdqu YMMWORD PTR [rdi+1664], ymm9
	vmovq xmm10, rcx
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1696], ymm10
	vmovq xmm10, rdx
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1728], ymm10
	vmovq xmm10, rbp
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1760], ymm10
	vmovq xmm10, r8
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1792], ymm10
	vmovq xmm10, r9
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1824], ymm10
	vmovq xmm10, r10
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1856], ymm10
	vmovdqu ymm11, YMMWORD PTR [rdi+64]
	vmovdqu ymm12, YMMWORD PTR [rdi+96]
	vmovdqu ymm13, YMMWORD PTR [rdi+128]
	vmovdqu ymm14, YMMWORD PTR [rdi+160]
	vpunpcklqdq ymm0, ymm11, ymm12
	vpunpckhqdq ymm1, ymm11, ymm12
	vpunpcklqdq ymm2, ymm13, ymm14
	vpunpckhqdq ymm3, ymm13, ymm14
	vperm2i128 ymm5, ymm0, ymm2, 32
	vperm2i128 ymm6, ymm1, ymm3, 32
	vperm2i128 ymm7, ymm0, ymm2, 49
	vperm2i128 ymm8, ymm1, ymm3, 49
	vpand ymm0, ymm5, ymm9
	vpsrlq ymm1, ymm5, 51
	vpsrlq ymm11, ymm9, 13
	vpand ymm11, ymm6, ymm11
	vpsllq ymm11, ymm11, 13
	vpor ymm1, ymm1, ymm11
	vpsrlq ymm2, ymm6, 38
	vpsrlq ymm11, ymm9, 26
	vpand ymm11, ymm7, ymm11
	vpsllq ymm11, ymm11, 26
	vpor ymm2, ymm2, ymm11
	vpsrlq ymm3, ymm7, 25
	vpsrlq ymm11, ymm9, 39
	vpand ymm11, ymm8, ymm11
	vpsllq ymm11, ymm11, 39
	vpor ymm3, ymm3, ymm11
	vpsrlq ymm4, ymm8, 12
	stmxcsr DWORD PTR [rdi+1600]
	mov r11d, DWORD PTR [rdi+1600]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rdi+1604], eax
	ldmxcsr DWORD PTR [rdi+1604]
	lfence
224:
	mov rbx, QWORD PTR [rdi+56]
	sub rbx, 1
	mov QWORD PTR [rdi+56], rbx
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	movzx ecx, BYTE PTR [rdi+rax*1+2049]
	or rbx, rcx
	jne 225f
	mov rbx, QWORD PTR [rdi+56]
	test rbx, rbx
	jmp 226f
225:
	cmp rax, rax
226:
	jne 224b
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	test rbx, rbx
	jne 227f
	jmp 228f
227:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5376
	add rax, rcx
	vmovdqu ymm11, YMMWORD PTR [rax]
	vmovdqu ymm12, YMMWORD PTR [rax+32]
	vmovdqu ymm13, YMMWORD PTR [rax+64]
	vmovdqu ymm14, YMMWORD PTR [rax+96]
	vpunpcklqdq ymm5, ymm11, ymm12
	vpunpckhqdq ymm6, ymm11, ymm12
	vpunpcklqdq ymm7, ymm13, ymm14
	vpunpckhqdq ymm8, ymm13, ymm14
	vperm2i128 ymm11, ymm5, ymm7, 32
	vperm2i128 ymm12, ymm6, ymm8, 32
	vperm2i128 ymm13, ymm5, ymm7, 49
	vperm2i128 ymm14, ymm6, ymm8, 49
	vmovdqu ymm15, YMMWORD PTR [rdi+1664]
	vpand ymm5, ymm11, ymm15
	vpsrlq ymm6, ymm11, 51
	vpsrlq ymm10, ymm15, 13
	vpand ymm10, ymm12, ymm10
	vpsllq ymm10, ymm10, 13
	vpor ymm6, ymm6, ymm10
	vpsrlq ymm7, ymm12, 38
	vpsrlq ymm10, ymm15, 26
	vpand ymm10, ymm13, ymm10
	vpsllq ymm10, ymm10, 26
	vpor ymm7, ymm7, ymm10
	vpsrlq ymm8, ymm13, 25
	vpsrlq ymm10, ymm15, 39
	vpand ymm10, ymm14, ymm10
	vpsllq ymm10, ymm10, 39
	vpor ymm8, ymm8, ymm10
	vpsrlq ymm9, ymm14, 12
	vpxor ymm13, ymm13, ymm13
	vpermq ymm10, ymm0, 181
	vpermq ymm11, ymm0, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm0, ymm10, ymm11
	vpermq ymm10, ymm1, 181
	vpermq ymm11, ymm1, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm1, ymm10, ymm11
	vpermq ymm10, ymm2, 181
	vpermq ymm11, ymm2, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm2, ymm10, ymm11
	vpermq ymm10, ymm3, 181
	vpermq ymm11, ymm3, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm3, ymm10, ymm11
	vpermq ymm10, ymm4, 181
	vpermq ymm11, ymm4, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm4, ymm10, ymm11
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1024], ymm0
	vmovdqu YMMWORD PTR [rdi+1056], ymm1
	vmovdqu YMMWORD PTR [rdi+1088], ymm2
	vmovdqu YMMWORD PTR [rdi+1120], ymm3
	vmovdqu YMMWORD PTR [rdi+1152], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vpermq ymm10, ymm0, 125
	vpermq ymm11, ymm0, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm0, ymm10, 36
	vpermq ymm5, ymm10, 222
	vpermq ymm10, ymm1, 125
	vpermq ymm11, ymm1, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm1, ymm10, 36
	vpermq ymm6, ymm10, 222
	vpermq ymm10, ymm2, 125
	vpermq ymm11, ymm2, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm2, ymm10, 36
	vpermq ymm7, ymm10, 222
	vpermq ymm10, ymm3, 125
	vpermq ymm11, ymm3, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm3, ymm10, 36
	vpermq ymm8, ymm10, 222
	vpermq ymm10, ymm4, 125
	vpermq ymm11, ymm4, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm4, ymm10, 36
	vpermq ymm9, ymm10, 222
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm9, 51
	vpand ymm9, ymm9, ymm10
	vpsrlq ymm12, ymm8, 51
	vpand ymm8, ymm8, ymm10
	vpaddq ymm9, ymm9, ymm12
	vpsrlq ymm12, ymm7, 51
	vpand ymm7, ymm7, ymm10
	vpaddq ymm8, ymm8, ymm12
	vpsrlq ymm12, ymm6, 51
	vpand ymm6, ymm6, ymm10
	vpaddq ymm7, ymm7, ymm12
	vpsrlq ymm12, ymm5, 51
	vpand ymm5, ymm5, ymm10
	vpaddq ymm6, ymm6, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm5, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1184], ymm0
	vmovdqu YMMWORD PTR [rdi+1216], ymm1
	vmovdqu YMMWORD PTR [rdi+1248], ymm2
	vmovdqu YMMWORD PTR [rdi+1280], ymm3
	vmovdqu YMMWORD PTR [rdi+1312], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
228:
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2049]
	test rbx, rbx
	jne 229f
	jmp 230f
229:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	mov rcx, QWORD PTR [rdi+7960]
	add rax, rcx
	vmovdqu ymm11, YMMWORD PTR [rax]
	vmovdqu ymm12, YMMWORD PTR [rax+32]
	vmovdqu ymm13, YMMWORD PTR [rax+64]
	vmovdqu ymm14, YMMWORD PTR [rax+96]
	vpunpcklqdq ymm5, ymm11, ymm12
	vpunpckhqdq ymm6, ymm11, ymm12
	vpunpcklqdq ymm7, ymm13, ymm14
	vpunpckhqdq ymm8, ymm13, ymm14
	vperm2i128 ymm11, ymm5, ymm7, 32
	vperm2i128 ymm12, ymm6, ymm8, 32
	vperm2i128 ymm13, ymm5, ymm7, 49
	vperm2i128 ymm14, ymm6, ymm8, 49
	vmovdqu ymm15, YMMWORD PTR [rdi+1664]
	vpand ymm5, ymm11, ymm15
	vpsrlq ymm6, ymm11, 51
	vpsrlq ymm10, ymm15, 13
	vpand ymm10, ymm12, ymm10
	vpsllq ymm10, ymm10, 13
	vpor ymm6, ymm6, ymm10
	vpsrlq ymm7, ymm12, 38
	vpsrlq ymm10, ymm15, 26
	vpand ymm10, ymm13, ymm10
	vpsllq ymm10, ymm10, 26
	vpor ymm7, ymm7, ymm10
	vpsrlq ymm8, ymm13, 25
	vpsrlq ymm10, ymm15, 39
	vpand ymm10, ymm14, ymm10
	vpsllq ymm10, ymm10, 39
	vpor ymm8, ymm8, ymm10
	vpsrlq ymm9, ymm14, 12
	vpxor ymm13, ymm13, ymm13
	vpermq ymm10, ymm0, 181
	vpermq ymm11, ymm0, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm0, ymm10, ymm11
	vpermq ymm10, ymm1, 181
	vpermq ymm11, ymm1, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm1, ymm10, ymm11
	vpermq ymm10, ymm2, 181
	vpermq ymm11, ymm2, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm2, ymm10, ymm11
	vpermq ymm10, ymm3, 181
	vpermq ymm11, ymm3, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm3, ymm10, ymm11
	vpermq ymm10, ymm4, 181
	vpermq ymm11, ymm4, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm4, ymm10, ymm11
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1024], ymm0
	vmovdqu YMMWORD PTR [rdi+1056], ymm1
	vmovdqu YMMWORD PTR [rdi+1088], ymm2
	vmovdqu YMMWORD PTR [rdi+1120], ymm3
	vmovdqu YMMWORD PTR [rdi+1152], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vpermq ymm10, ymm0, 125
	vpermq ymm11, ymm0, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm0, ymm10, 36
	vpermq ymm5, ymm10, 222
	vpermq ymm10, ymm1, 125
	vpermq ymm11, ymm1, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm1, ymm10, 36
	vpermq ymm6, ymm10, 222
	vpermq ymm10, ymm2, 125
	vpermq ymm11, ymm2, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm2, ymm10, 36
	vpermq ymm7, ymm10, 222
	vpermq ymm10, ymm3, 125
	vpermq ymm11, ymm3, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm3, ymm10, 36
	vpermq ymm8, ymm10, 222
	vpermq ymm10, ymm4, 125
	vpermq ymm11, ymm4, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm4, ymm10, 36
	vpermq ymm9, ymm10, 222
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm9, 51
	vpand ymm9, ymm9, ymm10
	vpsrlq ymm12, ymm8, 51
	vpand ymm8, ymm8, ymm10
	vpaddq ymm9, ymm9, ymm12
	vpsrlq ymm12, ymm7, 51
	vpand ymm7, ymm7, ymm10
	vpaddq ymm8, ymm8, ymm12
	vpsrlq ymm12, ymm6, 51
	vpand ymm6, ymm6, ymm10
	vpaddq ymm7, ymm7, ymm12
	vpsrlq ymm12, ymm5, 51
	vpand ymm5, ymm5, ymm10
	vpaddq ymm6, ymm6, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm5, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1184], ymm0
	vmovdqu YMMWORD PTR [rdi+1216], ymm1
	vmovdqu YMMWORD PTR [rdi+1248], ymm2
	vmovdqu YMMWORD PTR [rdi+1280], ymm3
	vmovdqu YMMWORD PTR [rdi+1312], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
230:
	mov rbx, QWORD PTR [rdi+56]
	test rbx, rbx
	jne 231f
	jmp 232f
231:
233:
	mov rbx, QWORD PTR [rdi+56]
	sub rbx, 1
	mov QWORD PTR [rdi+56], rbx
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vpermq ymm10, ymm0, 36
	vmovdqu YMMWORD PTR [rdi+1024], ymm10
	vpermq ymm5, ymm0, 100
	vpermq ymm10, ymm1, 36
	vmovdqu YMMWORD PTR [rdi+1056], ymm10
	vpermq ymm6, ymm1, 100
	vpermq ymm10, ymm2, 36
	vmovdqu YMMWORD PTR [rdi+1088], ymm10
	vpermq ymm7, ymm2, 100
	vpermq ymm10, ymm3, 36
	vmovdqu YMMWORD PTR [rdi+1120], ymm10
	vpermq ymm8, ymm3, 100
	vpermq ymm10, ymm4, 36
	vmovdqu YMMWORD PTR [rdi+1152], ymm10
	vpermq ymm9, ymm4, 100
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vpermq ymm10, ymm0, 225
	vpaddq ymm11, ymm0, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpaddq ymm12, ymm12, ymm0
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm0, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm5, ymm10, ymm13, 48
	vpermq ymm10, ymm1, 225
	vpaddq ymm11, ymm1, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm1
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm1, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm6, ymm10, ymm13, 48
	vpermq ymm10, ymm2, 225
	vpaddq ymm11, ymm2, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm2
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm2, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm7, ymm10, ymm13, 48
	vpermq ymm10, ymm3, 225
	vpaddq ymm11, ymm3, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm3
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm3, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm8, ymm10, ymm13, 48
	vpermq ymm10, ymm4, 225
	vpaddq ymm11, ymm4, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm4
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm4, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm9, ymm10, ymm13, 48
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm9, 51
	vpand ymm9, ymm9, ymm10
	vpsrlq ymm12, ymm8, 51
	vpand ymm8, ymm8, ymm10
	vpaddq ymm9, ymm9, ymm12
	vpsrlq ymm12, ymm7, 51
	vpand ymm7, ymm7, ymm10
	vpaddq ymm8, ymm8, ymm12
	vpsrlq ymm12, ymm6, 51
	vpand ymm6, ymm6, ymm10
	vpaddq ymm7, ymm7, ymm12
	vpsrlq ymm12, ymm5, 51
	vpand ymm5, ymm5, ymm10
	vpaddq ymm6, ymm6, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm5, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1184], ymm0
	vmovdqu YMMWORD PTR [rdi+1216], ymm1
	vmovdqu YMMWORD PTR [rdi+1248], ymm2
	vmovdqu YMMWORD PTR [rdi+1280], ymm3
	vmovdqu YMMWORD PTR [rdi+1312], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	test rbx, rbx
	jne 234f
	jmp 235f
234:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5376
	add rax, rcx
	vmovdqu ymm11, YMMWORD PTR [rax]
	vmovdqu ymm12, YMMWORD PTR [rax+32]
	vmovdqu ymm13, YMMWORD PTR [rax+64]
	vmovdqu ymm14, YMMWORD PTR [rax+96]
	vpunpcklqdq ymm5, ymm11, ymm12
	vpunpckhqdq ymm6, ymm11, ymm12
	vpunpcklqdq ymm7, ymm13, ymm14
	vpunpckhqdq ymm8, ymm13, ymm14
	vperm2i128 ymm11, ymm5, ymm7, 32
	vperm2i128 ymm12, ymm6, ymm8, 32
	vperm2i128 ymm13, ymm5, ymm7, 49
	vperm2i128 ymm14, ymm6, ymm8, 49
	vmovdqu ymm15, YMMWORD PTR [rdi+1664]
	vpand ymm5, ymm11, ymm15
	vpsrlq ymm6, ymm11, 51
	vpsrlq ymm10, ymm15, 13
	vpand ymm10, ymm12, ymm10
	vpsllq ymm10, ymm10, 13
	vpor ymm6, ymm6, ymm10
	vpsrlq ymm7, ymm12, 38
	vpsrlq ymm10, ymm15, 26
	vpand ymm10, ymm13, ymm10
	vpsllq ymm10, ymm10, 26
	vpor ymm7, ymm7, ymm10
	vpsrlq ymm8, ymm13, 25
	vpsrlq ymm10, ymm15, 39
	vpand ymm10, ymm14, ymm10
	vpsllq ymm10, ymm10, 39
	vpor ymm8, ymm8, ymm10
	vpsrlq ymm9, ymm14, 12
	vpxor ymm13, ymm13, ymm13
	vpermq ymm10, ymm0, 181
	vpermq ymm11, ymm0, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm0, ymm10, ymm11
	vpermq ymm10, ymm1, 181
	vpermq ymm11, ymm1, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm1, ymm10, ymm11
	vpermq ymm10, ymm2, 181
	vpermq ymm11, ymm2, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm2, ymm10, ymm11
	vpermq ymm10, ymm3, 181
	vpermq ymm11, ymm3, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm3, ymm10, ymm11
	vpermq ymm10, ymm4, 181
	vpermq ymm11, ymm4, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm4, ymm10, ymm11
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1024], ymm0
	vmovdqu YMMWORD PTR [rdi+1056], ymm1
	vmovdqu YMMWORD PTR [rdi+1088], ymm2
	vmovdqu YMMWORD PTR [rdi+1120], ymm3
	vmovdqu YMMWORD PTR [rdi+1152], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vpermq ymm10, ymm0, 125
	vpermq ymm11, ymm0, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm0, ymm10, 36
	vpermq ymm5, ymm10, 222
	vpermq ymm10, ymm1, 125
	vpermq ymm11, ymm1, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm1, ymm10, 36
	vpermq ymm6, ymm10, 222
	vpermq ymm10, ymm2, 125
	vpermq ymm11, ymm2, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm2, ymm10, 36
	vpermq ymm7, ymm10, 222
	vpermq ymm10, ymm3, 125
	vpermq ymm11, ymm3, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm3, ymm10, 36
	vpermq ymm8, ymm10, 222
	vpermq ymm10, ymm4, 125
	vpermq ymm11, ymm4, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm4, ymm10, 36
	vpermq ymm9, ymm10, 222
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm9, 51
	vpand ymm9, ymm9, ymm10
	vpsrlq ymm12, ymm8, 51
	vpand ymm8, ymm8, ymm10
	vpaddq ymm9, ymm9, ymm12
	vpsrlq ymm12, ymm7, 51
	vpand ymm7, ymm7, ymm10
	vpaddq ymm8, ymm8, ymm12
	vpsrlq ymm12, ymm6, 51
	vpand ymm6, ymm6, ymm10
	vpaddq ymm7, ymm7, ymm12
	vpsrlq ymm12, ymm5, 51
	vpand ymm5, ymm5, ymm10
	vpaddq ymm6, ymm6, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm5, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1184], ymm0
	vmovdqu YMMWORD PTR [rdi+1216], ymm1
	vmovdqu YMMWORD PTR [rdi+1248], ymm2
	vmovdqu YMMWORD PTR [rdi+1280], ymm3
	vmovdqu YMMWORD PTR [rdi+1312], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
235:
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2049]
	test rbx, rbx
	jne 236f
	jmp 237f
236:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	mov rcx, QWORD PTR [rdi+7960]
	add rax, rcx
	vmovdqu ymm11, YMMWORD PTR [rax]
	vmovdqu ymm12, YMMWORD PTR [rax+32]
	vmovdqu ymm13, YMMWORD PTR [rax+64]
	vmovdqu ymm14, YMMWORD PTR [rax+96]
	vpunpcklqdq ymm5, ymm11, ymm12
	vpunpckhqdq ymm6, ymm11, ymm12
	vpunpcklqdq ymm7, ymm13, ymm14
	vpunpckhqdq ymm8, ymm13, ymm14
	vperm2i128 ymm11, ymm5, ymm7, 32
	vperm2i128 ymm12, ymm6, ymm8, 32
	vperm2i128 ymm13, ymm5, ymm7, 49
	vperm2i128 ymm14, ymm6, ymm8, 49
	vmovdqu ymm15, YMMWORD PTR [rdi+1664]
	vpand ymm5, ymm11, ymm15
	vpsrlq ymm6, ymm11, 51
	vpsrlq ymm10, ymm15, 13
	vpand ymm10, ymm12, ymm10
	vpsllq ymm10, ymm10, 13
	vpor ymm6, ymm6, ymm10
	vpsrlq ymm7, ymm12, 38
	vpsrlq ymm10, ymm15, 26
	vpand ymm10, ymm13, ymm10
	vpsllq ymm10, ymm10, 26
	vpor ymm7, ymm7, ymm10
	vpsrlq ymm8, ymm13, 25
	vpsrlq ymm10, ymm15, 39
	vpand ymm10, ymm14, ymm10
	vpsllq ymm10, ymm10, 39
	vpor ymm8, ymm8, ymm10
	vpsrlq ymm9, ymm14, 12
	vpxor ymm13, ymm13, ymm13
	vpermq ymm10, ymm0, 181
	vpermq ymm11, ymm0, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm0, ymm10, ymm11
	vpermq ymm10, ymm1, 181
	vpermq ymm11, ymm1, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm1, ymm10, ymm11
	vpermq ymm10, ymm2, 181
	vpermq ymm11, ymm2, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm2, ymm10, ymm11
	vpermq ymm10, ymm3, 181
	vpermq ymm11, ymm3, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm3, ymm10, ymm11
	vpermq ymm10, ymm4, 181
	vpermq ymm11, ymm4, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm4, ymm10, ymm11
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1024], ymm0
	vmovdqu YMMWORD PTR [rdi+1056], ymm1
	vmovdqu YMMWORD PTR [rdi+1088], ymm2
	vmovdqu YMMWORD PTR [rdi+1120], ymm3
	vmovdqu YMMWORD PTR [rdi+1152], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vpermq ymm10, ymm0, 125
	vpermq ymm11, ymm0, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm0, ymm10, 36
	vpermq ymm5, ymm10, 222
	vpermq ymm10, ymm1, 125
	vpermq ymm11, ymm1, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm1, ymm10, 36
	vpermq ymm6, ymm10, 222
	vpermq ymm10, ymm2, 125
	vpermq ymm11, ymm2, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm2, ymm10, 36
	vpermq ymm7, ymm10, 222
	vpermq ymm10, ymm3, 125
	vpermq ymm11, ymm3, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm3, ymm10, 36
	vpermq ymm8, ymm10, 222
	vpermq ymm10, ymm4, 125
	vpermq ymm11, ymm4, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm4, ymm10, 36
	vpermq ymm9, ymm10, 222
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm9, 51
	vpand ymm9, ymm9, ymm10
	vpsrlq ymm12, ymm8, 51
	vpand ymm8, ymm8, ymm10
	vpaddq ymm9, ymm9, ymm12
	vpsrlq ymm12, ymm7, 51
	vpand ymm7, ymm7, ymm10
	vpaddq ymm8, ymm8, ymm12
	vpsrlq ymm12, ymm6, 51
	vpand ymm6, ymm6, ymm10
	vpaddq ymm7, ymm7, ymm12
	vpsrlq ymm12, ymm5, 51
	vpand ymm5, ymm5, ymm10
	vpaddq ymm6, ymm6, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm5, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1184], ymm0
	vmovdqu YMMWORD PTR [rdi+1216], ymm1
	vmovdqu YMMWORD PTR [rdi+1248], ymm2
	vmovdqu YMMWORD PTR [rdi+1280], ymm3
	vmovdqu YMMWORD PTR [rdi+1312], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
237:
	mov rbx, QWORD PTR [rdi+56]
	test rbx, rbx
	jne 233b
232:
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm11
	vpsrlq ymm11, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm11
	vpsrlq ymm11, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm11
	vpsrlq ymm11, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm11
	vmovdqu ymm11, YMMWORD PTR [rdi+1792]
	vpand ymm12, ymm1, ymm11
	vpsllq ymm12, ymm12, 51
	vpor ymm5, ymm0, ymm12
	vpsrlq ymm6, ymm1, 13
	vmovdqu ymm11, YMMWORD PTR [rdi+1824]
	vpand ymm12, ymm2, ymm11
	vpsllq ymm12, ymm12, 38
	vpor ymm6, ymm6, ymm12
	vpsrlq ymm7, ymm2, 26
	vmovdqu ymm11, YMMWORD PTR [rdi+1856]
	vpand ymm12, ymm3, ymm11
	vpsllq ymm12, ymm12, 25
	vpor ymm7, ymm7, ymm12
	vpsrlq ymm8, ymm3, 39
	vpsllq ymm12, ymm4, 12
	vpor ymm8, ymm8, ymm12
	vpunpcklqdq ymm0, ymm5, ymm6
	vpunpckhqdq ymm1, ymm5, ymm6
	vpunpcklqdq ymm2, ymm7, ymm8
	vpunpckhqdq ymm3, ymm7, ymm8
	vperm2i128 ymm5, ymm0, ymm2, 32
	vperm2i128 ymm6, ymm1, ymm3, 32
	vperm2i128 ymm7, ymm0, ymm2, 49
	vperm2i128 ymm8, ymm1, ymm3, 49
	vmovdqu YMMWORD PTR [rdi+64], ymm5
	vmovdqu YMMWORD PTR [rdi+96], ymm6
	vmovdqu YMMWORD PTR [rdi+128], ymm7
	vmovdqu YMMWORD PTR [rdi+160], ymm8
	vzeroupper
	lfence
	mov DWORD PTR [rdi+1600], r11d
	ldmxcsr DWORD PTR [rdi+1600]
	movabs rax, 7552
	add rax, rdi
	mov r8, QWORD PTR [rax]
	mov r9, QWORD PTR [rax+8]
	mov r10, QWORD PTR [rax+16]
	mov r11, QWORD PTR [rax+24]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov r8, QWORD PTR [rax+32]
	mov r9, QWORD PTR [rax+40]
	mov r10, QWORD PTR [rax+48]
	mov r11, QWORD PTR [rax+56]
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rax+64]
	mov r9, QWORD PTR [rax+72]
	mov r10, QWORD PTR [rax+80]
	mov r11, QWORD PTR [rax+88]
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov r8, QWORD PTR [rax+96]
	mov r9, QWORD PTR [rax+104]
	mov r10, QWORD PTR [rax+112]
	mov r11, QWORD PTR [rax+120]
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+344]
	sbb r11, QWORD PTR [rdi+216]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+288]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+296]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+304]
	mov r11, QWORD PTR [rdi+344]
	sbb r11, QWORD PTR [rdi+312]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
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
	mulx r13, rax, QWORD PTR [rdi+88]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
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
	mulx r14, rax, QWORD PTR [rdi+88]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+280]
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
	mulx r15, rax, QWORD PTR [rdi+88]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+96]
	mulx r10, rax, QWORD PTR [rdi+104]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
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
	mov rdx, QWORD PTR [rdi+272]
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
	mov rdx, QWORD PTR [rdi+280]
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
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov rdx, QWORD PTR [rdi+128]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+224]
	mulx r10, rax, QWORD PTR [rdi+232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+248]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+136]
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
	mov rdx, QWORD PTR [rdi+144]
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
	mov rdx, QWORD PTR [rdi+152]
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
	mov QWORD PTR [rdi+416], r8
	mov QWORD PTR [rdi+424], r9
	mov QWORD PTR [rdi+432], r10
	mov QWORD PTR [rdi+440], r11
	mov r8, QWORD PTR [rdi+320]
	sub r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+328]
	sbb r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+336]
	sbb r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+344]
	sbb r11, QWORD PTR [rdi+376]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
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
	mov rax, r8
	or rax, r9
	or rax, r10
	or rax, r11
	test rax, rax
	je 238f
	mov eax, 0
	jmp 239f
238:
	mov r8, QWORD PTR [rdi+384]
	sub r8, QWORD PTR [rdi+416]
	mov r9, QWORD PTR [rdi+392]
	sbb r9, QWORD PTR [rdi+424]
	mov r10, QWORD PTR [rdi+400]
	sbb r10, QWORD PTR [rdi+432]
	mov r11, QWORD PTR [rdi+408]
	sbb r11, QWORD PTR [rdi+440]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
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
	mov rax, r8
	or rax, r9
	or rax, r10
	or rax, r11
	test rax, rax
	je 240f
	mov eax, 0
	jmp 241f
240:
	mov eax, 1
241:
239:
25:
23:
21:
	mov rdx, rdi
	mov rbx, QWORD PTR [rdx]
	mov rbp, QWORD PTR [rdx+8]
	mov r12, QWORD PTR [rdx+16]
	mov r13, QWORD PTR [rdx+24]
	mov r14, QWORD PTR [rdx+32]
	mov r15, QWORD PTR [rdx+40]
	ret
	.p2align 6
