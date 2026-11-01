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
	mov rdx, QWORD PTR [rdi+7944]
	mov r8, QWORD PTR [rdx]
	mov r9, QWORD PTR [rdx+8]
	mov r10, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	movabs rax, 9223372036854775807
	and r11, rax
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	movabs r8, 8496970652267935907
	movabs r9, 31536524315187371
	movabs r10, -8302596497594521448
	movabs r11, 5909686906226998899
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+104]
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+120]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+96]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+104]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+112]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+120]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+248]
	sbb r11, QWORD PTR [rdi+216]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
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
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+120]
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
	mulx r15, rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+120]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov r8, QWORD PTR [rdi+288]
	add r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+296]
	adc r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+304]
	adc r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+312]
	adc r11, QWORD PTR [rdi+216]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rdx, QWORD PTR [rdi+288]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+296]
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+304]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+312]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+288]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+296]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+304]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+312]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov rdx, QWORD PTR [rdi+288]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+320]
	mulx r10, rax, QWORD PTR [rdi+328]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+336]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+344]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
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
	mov rdx, QWORD PTR [rdi+304]
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
	mov rdx, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov rdx, QWORD PTR [rdi+352]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+360]
	mulx r11, rax, QWORD PTR [rdi+368]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+376]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+360]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+376]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+368]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+376]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+352]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+360]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+368]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+376]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mulx r9, r8, QWORD PTR [rdi+384]
	mulx r10, rax, QWORD PTR [rdi+392]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+400]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+408]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+408]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+304]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+408]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+312]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+408]
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
	mov rdx, QWORD PTR [rdi+384]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+256]
	mulx r10, rax, QWORD PTR [rdi+264]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+272]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+280]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+392]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+280]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+400]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+280]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+408]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+280]
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
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov rdx, QWORD PTR [rdi+7936]
	mov r8, QWORD PTR [rdx]
	mov r9, QWORD PTR [rdx+8]
	mov r10, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	movabs rax, 9223372036854775807
	and r11, rax
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	movabs r8, 8496970652267935907
	movabs r9, 31536524315187371
	movabs r10, -8302596497594521448
	movabs r11, 5909686906226998899
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+104]
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+120]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+96]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+104]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+112]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+120]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+248]
	sbb r11, QWORD PTR [rdi+216]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
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
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+120]
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
	mulx r15, rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+120]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov r8, QWORD PTR [rdi+288]
	add r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+296]
	adc r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+304]
	adc r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+312]
	adc r11, QWORD PTR [rdi+216]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rdx, QWORD PTR [rdi+288]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+296]
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+304]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+312]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+288]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+296]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+304]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+312]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov rdx, QWORD PTR [rdi+288]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+320]
	mulx r10, rax, QWORD PTR [rdi+328]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+336]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+344]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
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
	mov rdx, QWORD PTR [rdi+304]
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
	mov rdx, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov rdx, QWORD PTR [rdi+352]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+360]
	mulx r11, rax, QWORD PTR [rdi+368]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+376]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+360]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+368]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+376]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+368]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+376]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+352]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+360]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+368]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+376]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mulx r9, r8, QWORD PTR [rdi+384]
	mulx r10, rax, QWORD PTR [rdi+392]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+400]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+408]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+408]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+304]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+408]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+312]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+408]
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
	mov rdx, QWORD PTR [rdi+384]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+256]
	mulx r10, rax, QWORD PTR [rdi+264]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+272]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+280]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+392]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+280]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+400]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+280]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+408]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+280]
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
	mov rdx, QWORD PTR [rdi+128]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+136]
	mulx r11, rax, QWORD PTR [rdi+144]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+152]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+136]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+152]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+144]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+152]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+128]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+136]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+144]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+152]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov rdx, QWORD PTR [rdi+160]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+168]
	mulx r11, rax, QWORD PTR [rdi+176]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+184]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+168]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+184]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+176]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+184]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+160]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+168]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+176]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+184]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+520]
	mulx r11, rax, QWORD PTR [rdi+528]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+536]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+528]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+536]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+536]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+512]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+520]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+528]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+536]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+640]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+648]
	mulx r11, rax, QWORD PTR [rdi+656]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+664]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+648]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+664]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+656]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+664]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+640]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+648]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+656]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+664]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+552]
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+568]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+544]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+552]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+560]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+568]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+680]
	mulx r11, rax, QWORD PTR [rdi+688]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+696]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+696]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+696]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+672]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+680]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+688]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+696]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+128]
	mulx r10, rax, QWORD PTR [rdi+136]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+144]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+152]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
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
	mov rdx, QWORD PTR [rdi+560]
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
	mov rdx, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+160]
	mulx r10, rax, QWORD PTR [rdi+168]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+176]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+184]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
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
	mov rdx, QWORD PTR [rdi+688]
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
	mov rdx, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
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
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+640]
	mulx r10, rax, QWORD PTR [rdi+648]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+656]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+664]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
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
	mulx r13, rax, QWORD PTR [rdi+664]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
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
	mulx r14, rax, QWORD PTR [rdi+664]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+696]
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
	mulx r15, rax, QWORD PTR [rdi+664]
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
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+520]
	mulx r11, rax, QWORD PTR [rdi+528]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+536]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+528]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+536]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+536]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+512]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+520]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+528]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+536]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+640]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+648]
	mulx r11, rax, QWORD PTR [rdi+656]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+664]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+648]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+656]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+664]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+656]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+664]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+640]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+648]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+656]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+664]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+544]
	mulx r10, rax, QWORD PTR [rdi+552]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+568]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+600]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+672]
	mulx r10, rax, QWORD PTR [rdi+680]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+688]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+696]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+696]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+696]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+728]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+552]
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+568]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+544]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+552]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+560]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+568]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+680]
	mulx r11, rax, QWORD PTR [rdi+688]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+696]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+696]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+696]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+672]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+680]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+688]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+696]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov ebx, 4
22:
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+712]
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+728]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+704]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+712]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+720]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+728]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	sub rbx, 1
	jne 22b
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
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
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
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
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
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
	mulx r15, rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+704]
	mulx r10, rax, QWORD PTR [rdi+712]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+728]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+696]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+728]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+552]
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+568]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+544]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+552]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+560]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+568]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+680]
	mulx r11, rax, QWORD PTR [rdi+688]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+696]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+696]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+696]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+672]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+680]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+688]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+696]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov ebx, 9
23:
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+712]
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+728]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+704]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+712]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+720]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+728]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	sub rbx, 1
	jne 23b
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
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
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
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
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
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
	mulx r15, rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+704]
	mulx r10, rax, QWORD PTR [rdi+712]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+728]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+696]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+728]
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+712]
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+728]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+704]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+712]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+720]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+728]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov ebx, 19
24:
	mov rdx, QWORD PTR [rdi+608]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+616]
	mulx r11, rax, QWORD PTR [rdi+624]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+632]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+616]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+632]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+624]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+632]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+608]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+616]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+624]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+632]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+744]
	mulx r11, rax, QWORD PTR [rdi+752]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+760]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+752]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+760]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+760]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+736]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+744]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+752]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+760]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	sub rbx, 1
	jne 24b
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+608]
	mulx r10, rax, QWORD PTR [rdi+616]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+624]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+632]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+632]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+632]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+600]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+632]
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+736]
	mulx r10, rax, QWORD PTR [rdi+744]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+752]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+760]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+736]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+744]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+752]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+760]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+736]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+744]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+752]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+760]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+728]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+736]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+744]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+752]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+760]
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+712]
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+728]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+704]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+712]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+720]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+728]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov ebx, 9
25:
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+712]
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+728]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+704]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+712]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+720]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+728]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	sub rbx, 1
	jne 25b
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
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
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
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
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
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
	mulx r15, rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+704]
	mulx r10, rax, QWORD PTR [rdi+712]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+728]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+696]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+728]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+552]
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+568]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+544]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+552]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+560]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+568]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+680]
	mulx r11, rax, QWORD PTR [rdi+688]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+696]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+696]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+696]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+672]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+680]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+688]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+696]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov ebx, 49
26:
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+712]
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+728]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+704]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+712]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+720]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+728]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	sub rbx, 1
	jne 26b
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
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
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
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
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
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
	mulx r15, rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+704]
	mulx r10, rax, QWORD PTR [rdi+712]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+728]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+696]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+728]
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+712]
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+728]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+704]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+712]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+720]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+728]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov ebx, 99
27:
	mov rdx, QWORD PTR [rdi+608]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+616]
	mulx r11, rax, QWORD PTR [rdi+624]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+632]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+616]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+632]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+624]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+632]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+608]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+616]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+624]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+632]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+744]
	mulx r11, rax, QWORD PTR [rdi+752]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+760]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+752]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+760]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+760]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+736]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+744]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+752]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+760]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	sub rbx, 1
	jne 27b
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+608]
	mulx r10, rax, QWORD PTR [rdi+616]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+624]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+632]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+632]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+632]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+600]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+608]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+616]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+624]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+632]
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+736]
	mulx r10, rax, QWORD PTR [rdi+744]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+752]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+760]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+736]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+744]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+752]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+760]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+736]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+744]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+752]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+760]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+728]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+736]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+744]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+752]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+760]
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+712]
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+728]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+704]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+712]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+720]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+728]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov ebx, 49
28:
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+712]
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+728]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+704]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+712]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+720]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+728]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	sub rbx, 1
	jne 28b
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
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
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
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
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
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
	mulx r15, rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+704]
	mulx r10, rax, QWORD PTR [rdi+712]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+720]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+728]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+728]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+728]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+696]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+704]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+712]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+720]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+728]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+552]
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+568]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+544]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+552]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+560]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+568]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+680]
	mulx r11, rax, QWORD PTR [rdi+688]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+696]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+696]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+696]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+672]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+680]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+688]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+696]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov ebx, 1
29:
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+552]
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+568]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+544]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+552]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+560]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+568]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+672]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+680]
	mulx r11, rax, QWORD PTR [rdi+688]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+696]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+680]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+696]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+688]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+696]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+672]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+680]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+688]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+696]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	sub rbx, 1
	jne 29b
	mov rdx, QWORD PTR [rdi+128]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+544]
	mulx r10, rax, QWORD PTR [rdi+552]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+136]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+144]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+568]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+152]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+160]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+672]
	mulx r10, rax, QWORD PTR [rdi+680]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+688]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+696]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+168]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+696]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+176]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+696]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+184]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+672]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+680]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+688]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rax, rdi
	mov r8, QWORD PTR [rdi+672]
	mov r9, QWORD PTR [rdi+680]
	mov r10, QWORD PTR [rdi+688]
	mov r11, QWORD PTR [rdi+696]
	mov QWORD PTR [rax+7680], r8
	mov QWORD PTR [rax+7688], r9
	mov QWORD PTR [rax+7696], r10
	mov QWORD PTR [rax+7704], r11
	mov rdx, QWORD PTR [rdi+7936]
	mov rsi, QWORD PTR [rdx+24]
	shr rsi, 63
	mov r8, QWORD PTR [rdx]
	mov r9, QWORD PTR [rdx+8]
	mov r10, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	movabs rax, 9223372036854775807
	and r11, rax
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	movabs rdx, 9223372036854775807
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
	test rcx, rcx
	je 210f
	mov eax, 0
	jmp 211f
210:
	movabs r8, 8496970652267935907
	movabs r9, 31536524315187371
	movabs r10, -8302596497594521448
	movabs r11, 5909686906226998899
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+104]
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+120]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+96]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+104]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+112]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+120]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+248]
	sbb r11, QWORD PTR [rdi+216]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
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
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+120]
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
	mulx r15, rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+120]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov r8, QWORD PTR [rdi+288]
	add r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+296]
	adc r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+304]
	adc r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+312]
	adc r11, QWORD PTR [rdi+216]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rdx, QWORD PTR [rdi+288]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+296]
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+304]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+312]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+288]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+296]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+304]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+312]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov rdx, QWORD PTR [rdi+288]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+320]
	mulx r10, rax, QWORD PTR [rdi+328]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+336]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+344]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
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
	mov rdx, QWORD PTR [rdi+304]
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
	mov rdx, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+248]
	sbb r11, QWORD PTR [rdi+280]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+448], r8
	mov QWORD PTR [rdi+456], r9
	mov QWORD PTR [rdi+464], r10
	mov QWORD PTR [rdi+472], r11
	mov rdx, QWORD PTR [rdi+352]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+256]
	mulx r10, rax, QWORD PTR [rdi+264]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+272]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+280]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+360]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+280]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+368]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+280]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+376]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+280]
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
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
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
	mov rdx, QWORD PTR [rdi+560]
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
	mov rdx, QWORD PTR [rdi+568]
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
	mov rdx, QWORD PTR [rdi+64]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+72]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+80]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+88]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
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
	mov rdx, QWORD PTR [rdi+64]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+416]
	mulx r10, rax, QWORD PTR [rdi+424]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+432]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+440]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+72]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+440]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+80]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+440]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+88]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+440]
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
	mov r8, QWORD PTR [rdi+416]
	sub r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+424]
	sbb r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+432]
	sbb r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+440]
	sbb r11, QWORD PTR [rdi+280]
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
	je 212f
	mov r8, QWORD PTR [rdi+416]
	sub r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+424]
	sbb r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+432]
	sbb r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+440]
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
	je 214f
	mov eax, 0
	jmp 215f
214:
	movabs r8, -4256434742258392912
	movabs r9, 3405592160176694392
	movabs r10, 3120150775007532967
	movabs r11, 3135389899092516619
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rdx, QWORD PTR [rdi+640]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+648]
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
	mov rdx, QWORD PTR [rdi+656]
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
	mov rdx, QWORD PTR [rdi+664]
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
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	je 216f
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	and rax, 1
	xor rax, rsi
	test rax, rax
	je 218f
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+248]
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
	jmp 219f
218:
219:
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mov rdx, QWORD PTR [rdi+112]
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
	mov rdx, QWORD PTR [rdi+120]
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
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 1
	jmp 217f
216:
	test rsi, rsi
	jne 220f
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	and rax, 1
	xor rax, rsi
	test rax, rax
	je 222f
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+248]
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
	jmp 223f
222:
223:
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mov rdx, QWORD PTR [rdi+112]
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
	mov rdx, QWORD PTR [rdi+120]
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
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 1
	jmp 221f
220:
	mov eax, 0
221:
217:
215:
	jmp 213f
212:
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	je 224f
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	and rax, 1
	xor rax, rsi
	test rax, rax
	je 226f
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+248]
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
	jmp 227f
226:
227:
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mov rdx, QWORD PTR [rdi+112]
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
	mov rdx, QWORD PTR [rdi+120]
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
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 1
	jmp 225f
224:
	test rsi, rsi
	jne 228f
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	and rax, 1
	xor rax, rsi
	test rax, rax
	je 230f
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+248]
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
	jmp 231f
230:
231:
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mov rdx, QWORD PTR [rdi+112]
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
	mov rdx, QWORD PTR [rdi+120]
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
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 1
	jmp 229f
228:
	mov eax, 0
229:
225:
213:
211:
	test rax, rax
	jne 232f
	mov eax, 0
	jmp 233f
232:
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
	mov rsi, QWORD PTR [rdx+24]
	shr rsi, 63
	mov r8, QWORD PTR [rdx]
	mov r9, QWORD PTR [rdx+8]
	mov r10, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	movabs rax, 9223372036854775807
	and r11, rax
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	movabs rdx, 9223372036854775807
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
	test rcx, rcx
	je 234f
	mov eax, 0
	jmp 235f
234:
	movabs r8, 8496970652267935907
	movabs r9, 31536524315187371
	movabs r10, -8302596497594521448
	movabs r11, 5909686906226998899
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+104]
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+120]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+96]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+104]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+112]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+120]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+248]
	sbb r11, QWORD PTR [rdi+216]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
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
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+120]
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
	mulx r15, rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+112]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+120]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov r8, QWORD PTR [rdi+288]
	add r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+296]
	adc r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+304]
	adc r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+312]
	adc r11, QWORD PTR [rdi+216]
	sbb rax, rax
	and rax, 38
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov rdx, QWORD PTR [rdi+288]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+296]
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+304]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+312]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+288]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+296]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+304]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+312]
	mulx r15, rax, rdx
	adcx r14, r14
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
	mov rdx, QWORD PTR [rdi+288]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+320]
	mulx r10, rax, QWORD PTR [rdi+328]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+336]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+344]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+296]
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
	mov rdx, QWORD PTR [rdi+304]
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
	mov rdx, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+248]
	sbb r11, QWORD PTR [rdi+280]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	sub r8, rax
	mov QWORD PTR [rdi+448], r8
	mov QWORD PTR [rdi+456], r9
	mov QWORD PTR [rdi+464], r10
	mov QWORD PTR [rdi+472], r11
	mov rdx, QWORD PTR [rdi+352]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+256]
	mulx r10, rax, QWORD PTR [rdi+264]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+272]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+280]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+360]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+280]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+368]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+280]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+376]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+256]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+264]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+272]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+280]
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
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
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
	mov rdx, QWORD PTR [rdi+560]
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
	mov rdx, QWORD PTR [rdi+568]
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
	mov rdx, QWORD PTR [rdi+64]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+288]
	mulx r10, rax, QWORD PTR [rdi+296]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+304]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+312]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+72]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+312]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+80]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+312]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+88]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+296]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+304]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+312]
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
	mov rdx, QWORD PTR [rdi+64]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+416]
	mulx r10, rax, QWORD PTR [rdi+424]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+432]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+440]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+72]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+440]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+80]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+440]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+88]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+416]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+424]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+432]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+440]
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
	mov r8, QWORD PTR [rdi+416]
	sub r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+424]
	sbb r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+432]
	sbb r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+440]
	sbb r11, QWORD PTR [rdi+280]
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
	je 236f
	mov r8, QWORD PTR [rdi+416]
	sub r8, QWORD PTR [rdi+448]
	mov r9, QWORD PTR [rdi+424]
	sbb r9, QWORD PTR [rdi+456]
	mov r10, QWORD PTR [rdi+432]
	sbb r10, QWORD PTR [rdi+464]
	mov r11, QWORD PTR [rdi+440]
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
	movabs r8, -4256434742258392912
	movabs r9, 3405592160176694392
	movabs r10, 3120150775007532967
	movabs r11, 3135389899092516619
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rdx, QWORD PTR [rdi+640]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+648]
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
	mov rdx, QWORD PTR [rdi+656]
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
	mov rdx, QWORD PTR [rdi+664]
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
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	and rax, 1
	xor rax, rsi
	test rax, rax
	je 242f
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+248]
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
	jmp 243f
242:
243:
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mov rdx, QWORD PTR [rdi+112]
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
	mov rdx, QWORD PTR [rdi+120]
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
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 1
	jmp 241f
240:
	test rsi, rsi
	jne 244f
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	and rax, 1
	xor rax, rsi
	test rax, rax
	je 246f
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+248]
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
	jmp 247f
246:
247:
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mov rdx, QWORD PTR [rdi+112]
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
	mov rdx, QWORD PTR [rdi+120]
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
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 1
	jmp 245f
244:
	mov eax, 0
245:
241:
239:
	jmp 237f
236:
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	and rax, 1
	xor rax, rsi
	test rax, rax
	je 250f
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+248]
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
	jmp 251f
250:
251:
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mov rdx, QWORD PTR [rdi+112]
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
	mov rdx, QWORD PTR [rdi+120]
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
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 1
	jmp 249f
248:
	test rsi, rsi
	jne 252f
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
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
	and rax, 1
	xor rax, rsi
	test rax, rax
	je 254f
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+224], r8
	mov QWORD PTR [rdi+232], r9
	mov QWORD PTR [rdi+240], r10
	mov QWORD PTR [rdi+248], r11
	mov r8, QWORD PTR [rdi+224]
	sub r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+232]
	sbb r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+240]
	sbb r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+248]
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
	jmp 255f
254:
255:
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov rdx, QWORD PTR [rdi+96]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+104]
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
	mov rdx, QWORD PTR [rdi+112]
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
	mov rdx, QWORD PTR [rdi+120]
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
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 1
	jmp 253f
252:
	mov eax, 0
253:
249:
237:
235:
	test rax, rax
	jne 256f
	mov eax, 0
	jmp 257f
256:
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
258:
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
	jne 258b
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
259:
	mov rbx, QWORD PTR [rdi+56]
	sub rbx, 1
	mov QWORD PTR [rdi+56], rbx
	mov rsi, QWORD PTR [rdi+7952]
	add rsi, 0
	mov rax, QWORD PTR [rdi+56]
	movzx ebx, BYTE PTR [rsi+rax*1]
	test rbx, rbx
	jne 260f
	mov rbx, QWORD PTR [rdi+56]
	cmp rbx, 32
	jmp 261f
260:
	mov rax, QWORD PTR [rdi+56]
	add rax, 1
	mov QWORD PTR [rdi+56], rax
	cmp rax, rax
261:
	jne 259b
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
262:
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
	je 263f
	and rbx, 31
	add rbx, r8
	cmp rbx, 16
	jb 265f
	mov eax, 33
	sub rax, rbx
	mov rbx, rax
	mov r8d, 1
	jmp 266f
265:
	mov r8d, 0
266:
	mov rax, rsi
	add rax, rax
	mov BYTE PTR [rdi+rax*1+2048], bl
	add rsi, 5
	jmp 264f
263:
	add rsi, 1
264:
	mov rax, QWORD PTR [rdi+56]
	shl rax, 3
	cmp rsi, rax
	jb 262b
	test r8, r8
	jne 267f
	jmp 268f
267:
	mov rax, rsi
	add rax, rax
	mov ebx, 1
	mov BYTE PTR [rdi+rax*1+2048], bl
268:
	mov esi, 0
	mov r8d, 0
269:
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
	je 270f
	and rbx, 255
	add rbx, r8
	cmp rbx, 128
	jb 272f
	mov eax, 257
	sub rax, rbx
	mov rbx, rax
	mov r8d, 1
	jmp 273f
272:
	mov r8d, 0
273:
	mov rax, rsi
	add rax, rax
	mov BYTE PTR [rdi+rax*1+2049], bl
	add rsi, 8
	jmp 271f
270:
	add rsi, 1
271:
	cmp rsi, 256
	jb 269b
	test r8, r8
	jne 274f
	jmp 275f
274:
	mov rax, rsi
	add rax, rax
	mov ebx, 1
	mov BYTE PTR [rdi+rax*1+2049], bl
275:
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
276:
	mov rbx, QWORD PTR [rdi+56]
	sub rbx, 1
	mov QWORD PTR [rdi+56], rbx
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	movzx ecx, BYTE PTR [rdi+rax*1+2049]
	or rbx, rcx
	jne 277f
	mov rbx, QWORD PTR [rdi+56]
	test rbx, rbx
	jmp 278f
277:
	cmp rax, rax
278:
	jne 276b
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2048]
	test rbx, rbx
	jne 279f
	jmp 280f
279:
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
280:
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2049]
	test rbx, rbx
	jne 281f
	jmp 282f
281:
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
282:
	mov rbx, QWORD PTR [rdi+56]
	test rbx, rbx
	jne 283f
	jmp 284f
283:
285:
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
	jne 286f
	jmp 287f
286:
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
287:
	mov rax, QWORD PTR [rdi+56]
	add rax, rax
	movzx ebx, BYTE PTR [rdi+rax*1+2049]
	test rbx, rbx
	jne 288f
	jmp 289f
288:
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
289:
	mov rbx, QWORD PTR [rdi+56]
	test rbx, rbx
	jne 285b
284:
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
	je 290f
	mov eax, 0
	jmp 291f
290:
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
	je 292f
	mov eax, 0
	jmp 293f
292:
	mov eax, 1
293:
291:
257:
233:
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
