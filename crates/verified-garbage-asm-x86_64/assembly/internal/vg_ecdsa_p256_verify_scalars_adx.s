// The functions of `src/internal/vg_ecdsa_p256_verify_scalars_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_verify_scalars_adx:
	mov rdx, QWORD PTR [rdi+1056]
	sub rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1064]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+1072]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1080]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1056]
	or rdx, QWORD PTR [rdi+1064]
	or rdx, QWORD PTR [rdi+1072]
	or rdx, QWORD PTR [rdi+1080]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+1024]
	sub rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1032]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+1040]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1048]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1024]
	or rdx, QWORD PTR [rdi+1032]
	or rdx, QWORD PTR [rdi+1040]
	or rdx, QWORD PTR [rdi+1048]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+1024]
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
	mov rdx, QWORD PTR [rdi+1032]
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
	mov rdx, QWORD PTR [rdi+1040]
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
	mov rdx, QWORD PTR [rdi+1048]
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
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	ret
	.p2align 6
