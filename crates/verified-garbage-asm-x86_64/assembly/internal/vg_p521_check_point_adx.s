// The functions of `src/internal/vg_p521_check_point_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_check_point_adx:
	movq xmm0, rbx
	movq xmm1, rbp
	movq xmm2, r12
	movq xmm3, r13
	movq xmm4, r14
	movq xmm5, r15
	mov rdx, QWORD PTR [rdi+2440]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+2448]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+2456]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+2464]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+2472]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+2480]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+2488]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+2496]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+2504]
	sbb rdx, QWORD PTR [rdi+128]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2656]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+2664]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+2672]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+2680]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+2688]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+2696]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+2704]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+2712]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+2720]
	sbb rdx, QWORD PTR [rdi+128]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	add rdi, 2872
	mov rdx, QWORD PTR [rdi-432]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+1152], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-424]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+1160], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-416]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+1168], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-408]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+1176], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-400]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+1184], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-392]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+1192], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-384]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+1200], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-376]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+1208], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-368]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+1216], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 1152
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1512
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2512
	add rdi, 2872
	mov rdx, QWORD PTR [rdi-216]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+1152], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-208]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+1160], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-200]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+1168], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-192]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+1176], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-184]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+1184], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-176]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+1192], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-168]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+1200], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-160]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+1208], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-152]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+1216], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 1152
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1440
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2584
	add rdi, 2584
	xor eax, eax
	mov QWORD PTR [rdi+1440], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi+1448], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi+1456], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi+1464], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi+1472], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi+1480], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi+1488], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi+1496], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi+1504], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1440]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1440], rdx
	mov rdx, QWORD PTR [rdi+1448]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1448], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1456]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1456], rdx
	mov rdx, QWORD PTR [rdi+1464]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1464], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1472]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1472], rdx
	mov rdx, QWORD PTR [rdi+1480]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1480], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1488]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1488], rdx
	mov rdx, QWORD PTR [rdi+1496]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1496], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1504]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1504], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, 1440
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1296
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2728
	add rdi, 2512
	xor eax, eax
	mov QWORD PTR [rdi+1512], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi+1520], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi+1528], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi+1536], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi+1544], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi+1552], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi+1560], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi+1568], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi+1576], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1512]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1512], rdx
	mov rdx, QWORD PTR [rdi+1520]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1520], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1528]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1528], rdx
	mov rdx, QWORD PTR [rdi+1536]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1536], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1544]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1544], rdx
	mov rdx, QWORD PTR [rdi+1552]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1552], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1560]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1560], rdx
	mov rdx, QWORD PTR [rdi+1568]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+1568], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+1576]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+1576], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, 1512
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1008
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 3016
	add rdi, 2512
	mov rdx, QWORD PTR [rdi+504]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+1512], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi+512]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+1520], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi+520]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+1528], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi+528]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+1536], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi+536]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+1544], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi+544]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+1552], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi+552]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+1560], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi+560]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+1568], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi+568]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+1576], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 1512
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -936
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 3088
	add rdi, 2512
	mov rdx, QWORD PTR [rdi-2016]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+1512], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-2008]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+1520], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-2000]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+1528], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-1992]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+1536], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-1984]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+1544], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-1976]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+1552], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-1968]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+1560], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-1960]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+1568], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-1952]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+1576], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 1512
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1008
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 3016
	add rdi, 3088
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2800
	add rdi, 2800
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 3088
	add rdi, 2728
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 3016
	mov rdx, QWORD PTR [rdi+3016]
	or rdx, QWORD PTR [rdi+3024]
	or rdx, QWORD PTR [rdi+3032]
	or rdx, QWORD PTR [rdi+3040]
	or rdx, QWORD PTR [rdi+3048]
	or rdx, QWORD PTR [rdi+3056]
	or rdx, QWORD PTR [rdi+3064]
	or rdx, QWORD PTR [rdi+3072]
	or rdx, QWORD PTR [rdi+3080]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rcx, QWORD PTR [rdi+3232]
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+2512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2800], rax
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+2520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2808], rax
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+2528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2816], rax
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+2536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2824], rax
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+2544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2832], rax
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+2552]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2840], rax
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+2560]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2848], rax
	mov rax, QWORD PTR [rdi+696]
	mov rdx, QWORD PTR [rdi+2568]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2856], rax
	mov rax, QWORD PTR [rdi+704]
	mov rdx, QWORD PTR [rdi+2576]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2864], rax
	mov rax, QWORD PTR [rdi+712]
	mov rdx, QWORD PTR [rdi+2584]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+720]
	mov rdx, QWORD PTR [rdi+2592]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+728]
	mov rdx, QWORD PTR [rdi+2600]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+736]
	mov rdx, QWORD PTR [rdi+2608]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+744]
	mov rdx, QWORD PTR [rdi+2616]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+752]
	mov rdx, QWORD PTR [rdi+2624]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+760]
	mov rdx, QWORD PTR [rdi+2632]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+768]
	mov rdx, QWORD PTR [rdi+2640]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+776]
	mov rdx, QWORD PTR [rdi+2648]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3224], rax
	movq rbx, xmm0
	movq rbp, xmm1
	movq r12, xmm2
	movq r13, xmm3
	movq r14, xmm4
	movq r15, xmm5
	ret
	.p2align 6
