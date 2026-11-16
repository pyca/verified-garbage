// The functions of `src/internal/vg_ed25519_decode_powers.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_decode_powers:
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
	mov r14, QWORD PTR [rdi+96]
	mov r15, QWORD PTR [rdi+104]
	mov rcx, QWORD PTR [rdi+112]
	mov rbp, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+576]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+576]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+584]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+584]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+592]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+576]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+592]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+600]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+584]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+600]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+592]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov r14, QWORD PTR [rdi+96]
	mov r15, QWORD PTR [rdi+104]
	mov rcx, QWORD PTR [rdi+112]
	mov rbp, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+288]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+288]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+296]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+296]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+304]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+288]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+304]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+312]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+296]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+312]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+304]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
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
	mov rcx, QWORD PTR [rdi+296]
	mov rbp, QWORD PTR [rdi+304]
	mov r15, QWORD PTR [rdi+312]
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+288]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+288]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+296]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+296]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+304]
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
	mov rax, QWORD PTR [rdi+288]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+304]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+312]
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
	mov r14, QWORD PTR [rdi+288]
	mov r15, QWORD PTR [rdi+296]
	mov rcx, QWORD PTR [rdi+304]
	mov rbp, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov rcx, QWORD PTR [rdi+360]
	mov rbp, QWORD PTR [rdi+368]
	mov r15, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+352]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+352]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+352]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+360]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+360]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+368]
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
	mov rax, QWORD PTR [rdi+352]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+360]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+368]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+376]
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
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov r14, QWORD PTR [rdi+288]
	mov r15, QWORD PTR [rdi+296]
	mov rcx, QWORD PTR [rdi+304]
	mov rbp, QWORD PTR [rdi+312]
	mov rax, QWORD PTR [rdi+384]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+384]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+392]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+392]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+400]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+384]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+400]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+408]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+392]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+408]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+400]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+408]
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
	mov r14, QWORD PTR [rdi+384]
	mov r15, QWORD PTR [rdi+392]
	mov rcx, QWORD PTR [rdi+400]
	mov rbp, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+256]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+256]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+264]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+264]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+272]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+256]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+272]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+280]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+264]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+280]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+272]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
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
	mov r14, QWORD PTR [rdi+96]
	mov r15, QWORD PTR [rdi+104]
	mov rcx, QWORD PTR [rdi+112]
	mov rbp, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+576]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+576]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+584]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+584]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+592]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+576]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+592]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+600]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+584]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+600]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+592]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+600]
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
	mov QWORD PTR [rdi+288], r8
	mov QWORD PTR [rdi+296], r9
	mov QWORD PTR [rdi+304], r10
	mov QWORD PTR [rdi+312], r11
	mov r14, QWORD PTR [rdi+96]
	mov r15, QWORD PTR [rdi+104]
	mov rcx, QWORD PTR [rdi+112]
	mov rbp, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+288]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+288]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+296]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+296]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+304]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+288]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+304]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+312]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+296]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+312]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+304]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+312]
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
	mov rcx, QWORD PTR [rdi+296]
	mov rbp, QWORD PTR [rdi+304]
	mov r15, QWORD PTR [rdi+312]
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+288]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+288]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+296]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+296]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+304]
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
	mov rax, QWORD PTR [rdi+288]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+304]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+312]
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
	mov r14, QWORD PTR [rdi+288]
	mov r15, QWORD PTR [rdi+296]
	mov rcx, QWORD PTR [rdi+304]
	mov rbp, QWORD PTR [rdi+312]
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
	mov QWORD PTR [rdi+352], r8
	mov QWORD PTR [rdi+360], r9
	mov QWORD PTR [rdi+368], r10
	mov QWORD PTR [rdi+376], r11
	mov rcx, QWORD PTR [rdi+360]
	mov rbp, QWORD PTR [rdi+368]
	mov r15, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+352]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+352]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+352]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+360]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+360]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+368]
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
	mov rax, QWORD PTR [rdi+352]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+360]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+368]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+376]
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
	mov QWORD PTR [rdi+384], r8
	mov QWORD PTR [rdi+392], r9
	mov QWORD PTR [rdi+400], r10
	mov QWORD PTR [rdi+408], r11
	mov r14, QWORD PTR [rdi+288]
	mov r15, QWORD PTR [rdi+296]
	mov rcx, QWORD PTR [rdi+304]
	mov rbp, QWORD PTR [rdi+312]
	mov rax, QWORD PTR [rdi+384]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+384]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+392]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+384]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+392]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+400]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+384]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+392]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+400]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+408]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+392]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+400]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+408]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+400]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+408]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+408]
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
	mov r14, QWORD PTR [rdi+384]
	mov r15, QWORD PTR [rdi+392]
	mov rcx, QWORD PTR [rdi+400]
	mov rbp, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+256]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+256]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+264]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+264]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+272]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+256]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+272]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+280]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+264]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+280]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+272]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+280]
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
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov rcx, QWORD PTR [rdi+168]
	mov rbp, QWORD PTR [rdi+176]
	mov r15, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+160]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+160]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+168]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+168]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+176]
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
	mov rax, QWORD PTR [rdi+160]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+168]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+176]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+184]
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
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rcx, QWORD PTR [rdi+520]
	mov rbp, QWORD PTR [rdi+528]
	mov r15, QWORD PTR [rdi+536]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+512]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+512]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+520]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+520]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+528]
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
	mov rax, QWORD PTR [rdi+512]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+520]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+528]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+536]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rcx, QWORD PTR [rdi+648]
	mov rbp, QWORD PTR [rdi+656]
	mov r15, QWORD PTR [rdi+664]
	mov rax, QWORD PTR [rdi+640]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+640]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+640]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+648]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+648]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+656]
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
	mov rax, QWORD PTR [rdi+640]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+648]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+656]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+664]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov rcx, QWORD PTR [rdi+552]
	mov rbp, QWORD PTR [rdi+560]
	mov r15, QWORD PTR [rdi+568]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+544]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+544]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+552]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+552]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+560]
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
	mov rax, QWORD PTR [rdi+544]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+560]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rcx, QWORD PTR [rdi+680]
	mov rbp, QWORD PTR [rdi+688]
	mov r15, QWORD PTR [rdi+696]
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+672]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+672]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+680]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+680]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+688]
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
	mov rax, QWORD PTR [rdi+672]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+688]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov r14, QWORD PTR [rdi+544]
	mov r15, QWORD PTR [rdi+552]
	mov rcx, QWORD PTR [rdi+560]
	mov rbp, QWORD PTR [rdi+568]
	mov rax, QWORD PTR [rdi+128]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+128]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+136]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+136]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+144]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+128]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+144]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+152]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+136]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+152]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+144]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+152]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov r14, QWORD PTR [rdi+672]
	mov r15, QWORD PTR [rdi+680]
	mov rcx, QWORD PTR [rdi+688]
	mov rbp, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
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
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r14, QWORD PTR [rdi+672]
	mov r15, QWORD PTR [rdi+680]
	mov rcx, QWORD PTR [rdi+688]
	mov rbp, QWORD PTR [rdi+696]
	mov rax, QWORD PTR [rdi+640]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+640]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+648]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+640]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+648]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+656]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+640]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+648]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+656]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+664]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+648]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+656]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+664]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+656]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+664]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+664]
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
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rcx, QWORD PTR [rdi+520]
	mov rbp, QWORD PTR [rdi+528]
	mov r15, QWORD PTR [rdi+536]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+512]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+512]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+520]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+520]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+528]
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
	mov rax, QWORD PTR [rdi+512]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+520]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+528]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+536]
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
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rcx, QWORD PTR [rdi+648]
	mov rbp, QWORD PTR [rdi+656]
	mov r15, QWORD PTR [rdi+664]
	mov rax, QWORD PTR [rdi+640]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+640]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+640]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+648]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+648]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+656]
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
	mov rax, QWORD PTR [rdi+640]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+648]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+656]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+664]
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
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov r14, QWORD PTR [rdi+576]
	mov r15, QWORD PTR [rdi+584]
	mov rcx, QWORD PTR [rdi+592]
	mov rbp, QWORD PTR [rdi+600]
	mov rax, QWORD PTR [rdi+544]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+544]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+552]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+552]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+560]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+544]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+560]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+568]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+552]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+568]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+560]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov r14, QWORD PTR [rdi+704]
	mov r15, QWORD PTR [rdi+712]
	mov rcx, QWORD PTR [rdi+720]
	mov rbp, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+672]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+672]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+680]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+680]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+688]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+672]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+688]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+696]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+680]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+696]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+688]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov QWORD PTR [rdi+512], rsi
	movabs rsi, 3210084860757546245
20:
	test rsi, 128
	jne 21f
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov r8, QWORD PTR [rdi+672]
	mov r9, QWORD PTR [rdi+680]
	mov r10, QWORD PTR [rdi+688]
	mov r11, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	jmp 22f
21:
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
22:
	mov rbx, rsi
	and rbx, 127
23:
	mov rcx, QWORD PTR [rdi+552]
	mov rbp, QWORD PTR [rdi+560]
	mov r15, QWORD PTR [rdi+568]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+544]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+544]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+552]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+552]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+560]
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
	mov rax, QWORD PTR [rdi+544]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+560]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rcx, QWORD PTR [rdi+680]
	mov rbp, QWORD PTR [rdi+688]
	mov r15, QWORD PTR [rdi+696]
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+672]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+672]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+680]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+680]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+688]
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
	mov rax, QWORD PTR [rdi+672]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+688]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	sub rbx, 1
	jne 23b
	mov r14, QWORD PTR [rdi+576]
	mov r15, QWORD PTR [rdi+584]
	mov rcx, QWORD PTR [rdi+592]
	mov rbp, QWORD PTR [rdi+600]
	mov rax, QWORD PTR [rdi+544]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+544]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+552]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+552]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+560]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+544]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+560]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+568]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+552]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+568]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+560]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov r14, QWORD PTR [rdi+704]
	mov r15, QWORD PTR [rdi+712]
	mov rcx, QWORD PTR [rdi+720]
	mov rbp, QWORD PTR [rdi+728]
	mov rax, QWORD PTR [rdi+672]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+672]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+680]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+680]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+688]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+672]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+688]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+696]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+680]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+696]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+688]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	test rsi, 256
	jne 24f
	jmp 25f
24:
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, QWORD PTR [rdi+672]
	mov r9, QWORD PTR [rdi+680]
	mov r10, QWORD PTR [rdi+688]
	mov r11, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
25:
	shr rsi, 9
	test rsi, rsi
	jne 20b
	mov rsi, QWORD PTR [rdi+512]
	mov rcx, QWORD PTR [rdi+552]
	mov rbp, QWORD PTR [rdi+560]
	mov r15, QWORD PTR [rdi+568]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+544]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+544]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+552]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+552]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+560]
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
	mov rax, QWORD PTR [rdi+544]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+560]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rcx, QWORD PTR [rdi+680]
	mov rbp, QWORD PTR [rdi+688]
	mov r15, QWORD PTR [rdi+696]
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+672]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+672]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+680]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+680]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+688]
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
	mov rax, QWORD PTR [rdi+672]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+688]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	mov ebx, 1
26:
	mov rcx, QWORD PTR [rdi+552]
	mov rbp, QWORD PTR [rdi+560]
	mov r15, QWORD PTR [rdi+568]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+544]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+544]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+552]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+552]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+560]
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
	mov rax, QWORD PTR [rdi+544]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+560]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rcx, QWORD PTR [rdi+680]
	mov rbp, QWORD PTR [rdi+688]
	mov r15, QWORD PTR [rdi+696]
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	mov r9, rax
	mov r10, rdx
	xor r11d, r11d
	xor r12d, r12d
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+672]
	mul rbp
	add r10, rax
	adc r11, rdx
	mov rax, QWORD PTR [rdi+672]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+680]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+680]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+688]
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
	mov rax, QWORD PTR [rdi+672]
	mul rax
	mov r8, rax
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+680]
	mul rax
	add r9, rbp
	adc r10, rax
	adc r11, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+688]
	mul rax
	add rcx, rcx
	adc r12, rax
	adc r13, rdx
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+696]
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
	mov QWORD PTR [rdi+672], r8
	mov QWORD PTR [rdi+680], r9
	mov QWORD PTR [rdi+688], r10
	mov QWORD PTR [rdi+696], r11
	sub rbx, 1
	jne 26b
	mov r14, QWORD PTR [rdi+128]
	mov r15, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+144]
	mov rbp, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+544]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+544]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+552]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+552]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+560]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+544]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+560]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+568]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+552]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+568]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+560]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+568]
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
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov r14, QWORD PTR [rdi+160]
	mov r15, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+176]
	mov rbp, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+672]
	mul r14
	mov r8, rax
	mov r9, rdx
	xor r10d, r10d
	xor r11d, r11d
	mov rax, QWORD PTR [rdi+672]
	mul r15
	add r9, rax
	adc r10, rdx
	mov rax, QWORD PTR [rdi+680]
	mul r14
	add r9, rax
	adc r10, rdx
	adc r11, 0
	xor r12d, r12d
	mov rax, QWORD PTR [rdi+672]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+680]
	mul r15
	add r10, rax
	adc r11, rdx
	adc r12, 0
	mov rax, QWORD PTR [rdi+688]
	mul r14
	add r10, rax
	adc r11, rdx
	adc r12, 0
	xor r13d, r13d
	mov rax, QWORD PTR [rdi+672]
	mul rbp
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+680]
	mul rcx
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+688]
	mul r15
	add r11, rax
	adc r12, rdx
	adc r13, 0
	mov rax, QWORD PTR [rdi+696]
	mul r14
	add r11, rax
	adc r12, rdx
	adc r13, 0
	xor r14d, r14d
	mov rax, QWORD PTR [rdi+680]
	mul rbp
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+688]
	mul rcx
	add r12, rax
	adc r13, rdx
	adc r14, 0
	mov rax, QWORD PTR [rdi+696]
	mul r15
	add r12, rax
	adc r13, rdx
	adc r14, 0
	xor r15d, r15d
	mov rax, QWORD PTR [rdi+688]
	mul rbp
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+696]
	mul rcx
	add r13, rax
	adc r14, rdx
	adc r15, 0
	mov rax, QWORD PTR [rdi+696]
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
	ret
	.p2align 6
