// The functions of `src/internal/vg_ecdsa_p256_verify_uv_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_verify_uv_adx:
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+1088]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rax, r8
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1096]
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
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rax, r9
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1104]
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
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rax, r10
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rdx, QWORD PTR [rdi+1112]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r11
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+1056]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rax, r8
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1064]
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
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rax, r9
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1072]
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
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rax, r10
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rdx, QWORD PTR [rdi+1080]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+392]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+400]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+408]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r11
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1312], r12
	mov QWORD PTR [rdi+1320], r13
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+1344]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1016]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rax, r8
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1352]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1016]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rax, r9
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1360]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1016]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rax, r10
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rdx, QWORD PTR [rdi+1368]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1016]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r11
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r8
	mov QWORD PTR [rdi+1400], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+1312]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1016]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rax, r8
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1320]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1016]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rax, r9
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1328]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1016]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rax, r10
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rdx, QWORD PTR [rdi+1336]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1016]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r11
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1408], r12
	mov QWORD PTR [rdi+1416], r13
	mov QWORD PTR [rdi+1424], r8
	mov QWORD PTR [rdi+1432], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+1376]
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
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rax, r8
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1384]
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
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rax, r9
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1392]
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
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rax, r10
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rdx, QWORD PTR [rdi+1400]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r11
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
	mov QWORD PTR [rdi+1168], r8
	mov QWORD PTR [rdi+1176], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+1408]
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
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rax, r8
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1416]
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
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rax, r9
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1424]
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
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rax, r10
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
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
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	mov rdx, QWORD PTR [rdi+1432]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+216]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r11
	movabs rcx, -3687945983376704433
	mul rcx
	mov rdx, rax
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+120]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	mov rax, r12
	sub rax, QWORD PTR [rdi+96]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+104]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+112]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+120]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r8
	mov QWORD PTR [rdi+1208], r9
	ret
	.p2align 6
