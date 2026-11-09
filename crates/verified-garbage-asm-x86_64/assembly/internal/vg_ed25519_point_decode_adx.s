// The functions of `src/internal/vg_ed25519_point_decode_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_point_decode_adx:
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
	je 20f
	mov eax, 0
	jmp 21f
20:
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
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
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
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
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
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
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
	je 22f
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
	je 24f
	mov eax, 0
	jmp 25f
24:
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
	je 26f
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
	je 28f
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
	jmp 29f
28:
29:
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
	mov eax, 1
	jmp 27f
26:
	test rsi, rsi
	jne 210f
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
	je 212f
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
	jmp 213f
212:
213:
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
	mov eax, 1
	jmp 211f
210:
	mov eax, 0
211:
27:
25:
	jmp 23f
22:
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
	je 214f
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
	je 216f
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
	jmp 217f
216:
217:
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
	mov eax, 1
	jmp 215f
214:
	test rsi, rsi
	jne 218f
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
	je 220f
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
	jmp 221f
220:
221:
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
	mov eax, 1
	jmp 219f
218:
	mov eax, 0
219:
215:
23:
21:
	ret
	.p2align 6
