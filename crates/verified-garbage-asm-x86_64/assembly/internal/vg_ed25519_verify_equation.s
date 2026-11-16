// The functions of `src/internal/vg_ed25519_verify_equation.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_verify_equation:
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
	call {vg_ed25519_decode_powers}
	mov rdx, QWORD PTR [rdi+7936]
	call {vg_ed25519_point_decode}
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
	call {vg_ed25519_point_decode}
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
	call {vg_ed25519_r64_double_ext}
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
	mov r14, QWORD PTR [rdi+576]
	mov r15, QWORD PTR [rdi+584]
	mov rcx, QWORD PTR [rdi+592]
	mov rbp, QWORD PTR [rdi+600]
	mov rax, QWORD PTR [rdi+160]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+160]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+168]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+168]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+176]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+160]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+168]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+176]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+184]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+168]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+176]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+184]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+176]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
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
	mov r14, QWORD PTR [rdi+576]
	mov r15, QWORD PTR [rdi+584]
	mov rcx, QWORD PTR [rdi+592]
	mov rbp, QWORD PTR [rdi+600]
	mov rax, QWORD PTR [rdi+160]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+160]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+168]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+168]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+176]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+160]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+168]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+176]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+184]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+168]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+176]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+184]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+176]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
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
	mov r14, QWORD PTR [rdi+576]
	mov r15, QWORD PTR [rdi+584]
	mov rcx, QWORD PTR [rdi+592]
	mov rbp, QWORD PTR [rdi+600]
	mov rax, QWORD PTR [rdi+160]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+160]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+168]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+168]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+176]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+160]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+168]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+176]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+184]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+168]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+176]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+184]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+176]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
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
	call {vg_ed25519_r64_add_cached_ext}
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
	mov r14, QWORD PTR [rdi+576]
	mov r15, QWORD PTR [rdi+584]
	mov rcx, QWORD PTR [rdi+592]
	mov rbp, QWORD PTR [rdi+600]
	mov rax, QWORD PTR [rdi+160]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+160]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+168]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+168]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+176]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+160]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+168]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+176]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+184]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+168]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+176]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+184]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+176]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
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
	mov r14, QWORD PTR [rdi+576]
	mov r15, QWORD PTR [rdi+584]
	mov rcx, QWORD PTR [rdi+592]
	mov rbp, QWORD PTR [rdi+600]
	mov rax, QWORD PTR [rdi+160]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+160]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+168]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+168]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+176]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+160]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+168]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+176]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+184]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+168]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+176]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+184]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+176]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
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
	movzx ebx, BYTE PTR [rdi+rax*1+2049]
	test rbx, rbx
	jne 227f
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	test rbx, rbx
	jne 229f
	jmp 230f
229:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5376
	add rax, rcx
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
	call {vg_ed25519_r64_add_cached_proj}
230:
	jmp 228f
227:
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	test rbx, rbx
	jne 231f
	jmp 232f
231:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5376
	add rax, rcx
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
	call {vg_ed25519_r64_add_cached_ext}
232:
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2049]
	test rbx, rbx
	jne 233f
	jmp 234f
233:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	mov rcx, QWORD PTR [rdi+7960]
	add rax, rcx
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
	call {vg_ed25519_r64_add_cached_proj}
234:
228:
	mov rbx, QWORD PTR [rdi+56]
	test rbx, rbx
	jne 235f
	jmp 236f
235:
237:
	mov rbx, QWORD PTR [rdi+56]
	sub rbx, 1
	mov QWORD PTR [rdi+56], rbx
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	movzx ecx, BYTE PTR [rdi+rax*1+2049]
	or rbx, rcx
	jne 238f
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
	mov r8, QWORD PTR [rdi+384]
	sub r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+392]
	sbb r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+400]
	sbb r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+408]
	sbb r11, QWORD PTR [rdi+472]
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
	mov r8, QWORD PTR [rdi+320]
	add r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+328]
	adc r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+336]
	adc r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+344]
	adc r11, QWORD PTR [rdi+376]
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
	jmp 239f
238:
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
	mov r8, QWORD PTR [rdi+384]
	sub r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+392]
	sbb r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+400]
	sbb r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+408]
	sbb r11, QWORD PTR [rdi+472]
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
	mov r8, QWORD PTR [rdi+320]
	add r8, QWORD PTR [rdi+352]
	mov r9, QWORD PTR [rdi+328]
	adc r9, QWORD PTR [rdi+360]
	mov r10, QWORD PTR [rdi+336]
	adc r10, QWORD PTR [rdi+368]
	mov r11, QWORD PTR [rdi+344]
	adc r11, QWORD PTR [rdi+376]
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
239:
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2049]
	test rbx, rbx
	jne 240f
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	test rbx, rbx
	jne 242f
	jmp 243f
242:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5376
	add rax, rcx
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
	call {vg_ed25519_r64_add_cached_proj}
243:
	jmp 241f
240:
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	test rbx, rbx
	jne 244f
	jmp 245f
244:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	add rax, rdi
	movabs rcx, 5376
	add rax, rcx
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
	call {vg_ed25519_r64_add_cached_ext}
245:
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2049]
	test rbx, rbx
	jne 246f
	jmp 247f
246:
	sub rbx, 1
	mov rax, rbx
	movabs rcx, 128
	mul rcx
	mov rcx, QWORD PTR [rdi+7960]
	add rax, rcx
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
	mov r14, QWORD PTR [rdi+192]
	mov r15, QWORD PTR [rdi+200]
	mov rcx, QWORD PTR [rdi+208]
	mov rbp, QWORD PTR [rdi+216]
	mov rax, QWORD PTR [rdi+320]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+320]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+328]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+328]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+336]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+320]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+328]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+336]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+344]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+328]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+336]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+344]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+336]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+344]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+344]
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
	mov r14, QWORD PTR [rdi+224]
	mov r15, QWORD PTR [rdi+232]
	mov rcx, QWORD PTR [rdi+240]
	mov rbp, QWORD PTR [rdi+248]
	mov rax, QWORD PTR [rdi+352]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+352]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+360]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+352]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+360]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+368]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+352]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+360]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+368]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+376]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+360]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+368]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+376]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+368]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+376]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+376]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov r14, QWORD PTR [rdi+256]
	mov r15, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+272]
	mov rbp, QWORD PTR [rdi+280]
	mov rax, QWORD PTR [rdi+160]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+160]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+168]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+168]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+176]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+160]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+168]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+176]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+184]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+168]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+176]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+184]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+176]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+184]
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
	mov r14, QWORD PTR [rdi+480]
	mov r15, QWORD PTR [rdi+488]
	mov rcx, QWORD PTR [rdi+496]
	mov rbp, QWORD PTR [rdi+504]
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
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov r14, QWORD PTR [rdi+544]
	mov r15, QWORD PTR [rdi+552]
	mov rcx, QWORD PTR [rdi+560]
	mov rbp, QWORD PTR [rdi+568]
	mov rax, QWORD PTR [rdi+512]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+512]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+520]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+520]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+528]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+512]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+528]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+536]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+520]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+536]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+528]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+536]
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
	mov r14, QWORD PTR [rdi+512]
	mov r15, QWORD PTR [rdi+520]
	mov rcx, QWORD PTR [rdi+528]
	mov rbp, QWORD PTR [rdi+536]
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
247:
241:
	mov rbx, QWORD PTR [rdi+56]
	test rbx, rbx
	jne 237b
236:
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
	mov r14, QWORD PTR [rdi+256]
	mov r15, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+272]
	mov rbp, QWORD PTR [rdi+280]
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
	mov r14, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov rbp, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+192]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+192]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+200]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+200]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+208]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+192]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+208]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+216]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+200]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+216]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+208]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+216]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov r14, QWORD PTR [rdi+256]
	mov r15, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+272]
	mov rbp, QWORD PTR [rdi+280]
	mov rax, QWORD PTR [rdi+96]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+96]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+104]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+104]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+112]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+96]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+112]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+120]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+104]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+120]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+112]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+120]
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
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov r14, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov rbp, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+224]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+224]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+232]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+232]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+240]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+224]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+240]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+248]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+232]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+248]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+240]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+248]
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
	je 248f
	mov eax, 0
	jmp 249f
248:
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
	je 250f
	mov eax, 0
	jmp 251f
250:
	mov eax, 1
251:
249:
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
