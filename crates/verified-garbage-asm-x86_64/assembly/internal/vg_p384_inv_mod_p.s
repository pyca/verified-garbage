// The functions of `src/internal/vg_p384_inv_mod_p.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_inv_mod_p:
	mov QWORD PTR [rdi+1504], rbx
	mov QWORD PTR [rdi+1512], rbp
	mov QWORD PTR [rdi+1520], r12
	mov QWORD PTR [rdi+1528], r13
	mov QWORD PTR [rdi+1536], r14
	mov QWORD PTR [rdi+1544], r15
	mov ebx, 1
	mov r14d, 15
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3440], rax
	mov r8d, 0
	mov QWORD PTR [rdi+3448], r8
	mov rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+3456], rax
	mov rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+3464], rax
	mov rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+3472], rax
	mov rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+3480], rax
	mov rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+3488], rax
	mov rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+3496], rax
	mov r8d, 0
	mov QWORD PTR [rdi+3504], r8
	mov r8d, 0
	mov QWORD PTR [rdi+3512], r8
	mov QWORD PTR [rdi+3520], r8
	mov QWORD PTR [rdi+3528], r8
	mov QWORD PTR [rdi+3536], r8
	mov QWORD PTR [rdi+3544], r8
	mov QWORD PTR [rdi+3552], r8
	mov QWORD PTR [rdi+3560], r8
	mov r8d, 0
	mov QWORD PTR [rdi+3568], r8
	mov QWORD PTR [rdi+3576], r8
	mov QWORD PTR [rdi+3584], r8
	mov QWORD PTR [rdi+3592], r8
	mov QWORD PTR [rdi+3600], r8
	mov QWORD PTR [rdi+3608], r8
	mov QWORD PTR [rdi+3616], r8
	mov r8d, 1
	mov QWORD PTR [rdi+3568], r8
20:
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+3736], rax
	mov rax, QWORD PTR [rdi+3456]
	mov QWORD PTR [rdi+3744], rax
	xor rbx, -1
	mov r8, QWORD PTR [rdi+3736]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+3744]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi+3736]
	mul r8
	mov QWORD PTR [rdi+3752], rax
	mov rax, QWORD PTR [rdi+3744]
	mul rcx
	add rax, QWORD PTR [rdi+3752]
	shr rax, 15
	mov QWORD PTR [rdi+3752], rax
	mov rax, QWORD PTR [rdi+3736]
	mul r13
	mov QWORD PTR [rdi+3736], rax
	mov rax, QWORD PTR [rdi+3744]
	mul rbp
	add rax, QWORD PTR [rdi+3736]
	shr rax, 15
	mov QWORD PTR [rdi+3744], rax
	mov rax, QWORD PTR [rdi+3752]
	mov QWORD PTR [rdi+3736], rax
	mov r9, r8
	mov r10, rcx
	mov r11, r13
	mov r12, rbp
	mov r8, QWORD PTR [rdi+3736]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+3744]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi+3736]
	mul r8
	mov QWORD PTR [rdi+3752], rax
	mov rax, QWORD PTR [rdi+3744]
	mul rcx
	add rax, QWORD PTR [rdi+3752]
	shr rax, 15
	mov QWORD PTR [rdi+3752], rax
	mov rax, QWORD PTR [rdi+3736]
	mul r13
	mov QWORD PTR [rdi+3736], rax
	mov rax, QWORD PTR [rdi+3744]
	mul rbp
	add rax, QWORD PTR [rdi+3736]
	shr rax, 15
	mov QWORD PTR [rdi+3744], rax
	mov rax, QWORD PTR [rdi+3752]
	mov QWORD PTR [rdi+3736], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+3752], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+3752]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+3752], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+3752]
	mov r12, rax
	mov r8, QWORD PTR [rdi+3736]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+3744]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 49
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, QWORD PTR [rdi+3736]
	mul r8
	mov QWORD PTR [rdi+3752], rax
	mov rax, QWORD PTR [rdi+3744]
	mul rcx
	add rax, QWORD PTR [rdi+3752]
	shr rax, 15
	mov QWORD PTR [rdi+3752], rax
	mov rax, QWORD PTR [rdi+3736]
	mul r13
	mov QWORD PTR [rdi+3736], rax
	mov rax, QWORD PTR [rdi+3744]
	mul rbp
	add rax, QWORD PTR [rdi+3736]
	shr rax, 15
	mov QWORD PTR [rdi+3744], rax
	mov rax, QWORD PTR [rdi+3752]
	mov QWORD PTR [rdi+3736], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+3752], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+3752]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+3752], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+3752]
	mov r12, rax
	mov r8, QWORD PTR [rdi+3736]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+3744]
	and r13, 32767
	movabs rax, 140737488355328
	add r13, rax
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 63
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 62
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 61
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 60
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 59
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 58
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 57
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 56
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 55
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 54
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 53
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 52
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov rax, r13
	add rax, r8
	mov rdx, r13
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, r13
	shl rbp, 51
	cmove rax, r13
	add rbp, rbx
	cmovb rax, rdx
	cmovb r8, r13
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	mov r13, rax
	add r13, r8
	mov rdx, rax
	sub rdx, r8
	mov rcx, -2
	sub rcx, rbx
	mov rbp, rax
	shl rbp, 50
	cmove r13, rax
	add rbp, rbx
	cmovb r13, rdx
	cmovb r8, rax
	cmovb rbx, rcx
	add r8, r8
	sub rbx, 2
	movabs rcx, 2305878194659524608
	add r8, rcx
	add r13, rcx
	mov rcx, r8
	shr rcx, 47
	sub rcx, 16384
	shl r8, 17
	shr r8, 48
	sub r8, 16384
	mov rbp, r13
	shr rbp, 47
	sub rbp, 16384
	shl r13, 17
	shr r13, 48
	sub r13, 16384
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+3752], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+3752]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+3752], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+3752]
	mov r12, rax
	xor rbx, -1
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3800], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3808], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+3800]
	mov rax, rbp
	and rax, QWORD PTR [rdi+3808]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3400]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3456]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3736], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3408]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3464]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3744], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3416]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3472]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3752], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3424]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3480]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3760], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3432]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3488]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3768], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3440]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3496]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3776], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3448]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3504]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3784], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3736]
	mov r8, QWORD PTR [rdi+3744]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3624], rax
	mov rax, QWORD PTR [rdi+3744]
	mov r8, QWORD PTR [rdi+3752]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3632], rax
	mov rax, QWORD PTR [rdi+3752]
	mov r8, QWORD PTR [rdi+3760]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3640], rax
	mov rax, QWORD PTR [rdi+3760]
	mov r8, QWORD PTR [rdi+3768]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3648], rax
	mov rax, QWORD PTR [rdi+3768]
	mov r8, QWORD PTR [rdi+3776]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3656], rax
	mov rax, QWORD PTR [rdi+3776]
	mov r8, QWORD PTR [rdi+3784]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3664], rax
	mov rdx, QWORD PTR [rdi+3784]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3672], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3800], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3808], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+3800]
	mov rax, rbp
	and rax, QWORD PTR [rdi+3808]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3400]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3456]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3736], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3408]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3464]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3744], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3416]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3472]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3752], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3424]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3480]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3760], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3432]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3488]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3768], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3440]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3496]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3776], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3448]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3504]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3784], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3736]
	mov r8, QWORD PTR [rdi+3744]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3680], rax
	mov rax, QWORD PTR [rdi+3744]
	mov r8, QWORD PTR [rdi+3752]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3688], rax
	mov rax, QWORD PTR [rdi+3752]
	mov r8, QWORD PTR [rdi+3760]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3696], rax
	mov rax, QWORD PTR [rdi+3760]
	mov r8, QWORD PTR [rdi+3768]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3704], rax
	mov rax, QWORD PTR [rdi+3768]
	mov r8, QWORD PTR [rdi+3776]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3712], rax
	mov rax, QWORD PTR [rdi+3776]
	mov r8, QWORD PTR [rdi+3784]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3720], rax
	mov rdx, QWORD PTR [rdi+3784]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3728], rax
	mov rax, QWORD PTR [rdi+3624]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+3632]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+3640]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+3648]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+3656]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+3664]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+3672]
	mov QWORD PTR [rdi+3448], rax
	mov rax, QWORD PTR [rdi+3680]
	mov QWORD PTR [rdi+3456], rax
	mov rax, QWORD PTR [rdi+3688]
	mov QWORD PTR [rdi+3464], rax
	mov rax, QWORD PTR [rdi+3696]
	mov QWORD PTR [rdi+3472], rax
	mov rax, QWORD PTR [rdi+3704]
	mov QWORD PTR [rdi+3480], rax
	mov rax, QWORD PTR [rdi+3712]
	mov QWORD PTR [rdi+3488], rax
	mov rax, QWORD PTR [rdi+3720]
	mov QWORD PTR [rdi+3496], rax
	mov rax, QWORD PTR [rdi+3728]
	mov QWORD PTR [rdi+3504], rax
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3800], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3808], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+3800]
	mov rax, rbp
	and rax, QWORD PTR [rdi+3808]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3512]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3568]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3736], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3520]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3576]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3744], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3528]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3584]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3752], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3536]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3592]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3760], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3544]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3600]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3768], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3552]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3608]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3776], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3560]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3616]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3784], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3736]
	movabs rcx, 4294967297
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+3784]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+3792], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+3736]
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3736], r8
	mov r8, QWORD PTR [rdi+3744]
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3744], r8
	mov r8, QWORD PTR [rdi+3752]
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3752], r8
	mov r8, QWORD PTR [rdi+3760]
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3760], r8
	mov r8, QWORD PTR [rdi+3768]
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3768], r8
	mov r8, QWORD PTR [rdi+3776]
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3776], r8
	mov r8, QWORD PTR [rdi+3784]
	add r8, rbp
	mov QWORD PTR [rdi+3784], r8
	mov r8, QWORD PTR [rdi+3792]
	adc r8, 0
	mov QWORD PTR [rdi+3792], r8
	mov rax, QWORD PTR [rdi+3744]
	mov QWORD PTR [rdi+3624], rax
	mov rax, QWORD PTR [rdi+3752]
	mov QWORD PTR [rdi+3632], rax
	mov rax, QWORD PTR [rdi+3760]
	mov QWORD PTR [rdi+3640], rax
	mov rax, QWORD PTR [rdi+3768]
	mov QWORD PTR [rdi+3648], rax
	mov rax, QWORD PTR [rdi+3776]
	mov QWORD PTR [rdi+3656], rax
	mov rax, QWORD PTR [rdi+3784]
	mov QWORD PTR [rdi+3664], rax
	mov rax, QWORD PTR [rdi+3792]
	mov QWORD PTR [rdi+3672], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3800], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3808], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+3800]
	mov rax, rbp
	and rax, QWORD PTR [rdi+3808]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3512]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3568]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3736], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3520]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3576]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3744], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3528]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3584]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3752], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3536]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3592]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3760], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3544]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3600]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3768], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3552]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3608]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3776], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3560]
	xor rax, QWORD PTR [rdi+3800]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3616]
	xor rax, QWORD PTR [rdi+3808]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3784], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3736]
	movabs rcx, 4294967297
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+3784]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+3792], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+3736]
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3736], r8
	mov r8, QWORD PTR [rdi+3744]
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3744], r8
	mov r8, QWORD PTR [rdi+3752]
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3752], r8
	mov r8, QWORD PTR [rdi+3760]
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3760], r8
	mov r8, QWORD PTR [rdi+3768]
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3768], r8
	mov r8, QWORD PTR [rdi+3776]
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3776], r8
	mov r8, QWORD PTR [rdi+3784]
	add r8, rbp
	mov QWORD PTR [rdi+3784], r8
	mov r8, QWORD PTR [rdi+3792]
	adc r8, 0
	mov QWORD PTR [rdi+3792], r8
	mov rax, QWORD PTR [rdi+3744]
	mov QWORD PTR [rdi+3568], rax
	mov rax, QWORD PTR [rdi+3752]
	mov QWORD PTR [rdi+3576], rax
	mov rax, QWORD PTR [rdi+3760]
	mov QWORD PTR [rdi+3584], rax
	mov rax, QWORD PTR [rdi+3768]
	mov QWORD PTR [rdi+3592], rax
	mov rax, QWORD PTR [rdi+3776]
	mov QWORD PTR [rdi+3600], rax
	mov rax, QWORD PTR [rdi+3784]
	mov QWORD PTR [rdi+3608], rax
	mov rax, QWORD PTR [rdi+3792]
	mov QWORD PTR [rdi+3616], rax
	mov rax, QWORD PTR [rdi+3624]
	mov QWORD PTR [rdi+3512], rax
	mov rax, QWORD PTR [rdi+3632]
	mov QWORD PTR [rdi+3520], rax
	mov rax, QWORD PTR [rdi+3640]
	mov QWORD PTR [rdi+3528], rax
	mov rax, QWORD PTR [rdi+3648]
	mov QWORD PTR [rdi+3536], rax
	mov rax, QWORD PTR [rdi+3656]
	mov QWORD PTR [rdi+3544], rax
	mov rax, QWORD PTR [rdi+3664]
	mov QWORD PTR [rdi+3552], rax
	mov rax, QWORD PTR [rdi+3672]
	mov QWORD PTR [rdi+3560], rax
	sub r14, 1
	jne 20b
	mov r8d, 0
	mov QWORD PTR [rdi+3728], r8
	mov rdx, QWORD PTR [rdi+3560]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+64]
	and r8, r13
	mov QWORD PTR [rdi+3680], r8
	mov r8, QWORD PTR [rdi+72]
	and r8, r13
	mov QWORD PTR [rdi+3688], r8
	mov r8, QWORD PTR [rdi+80]
	and r8, r13
	mov QWORD PTR [rdi+3696], r8
	mov r8, QWORD PTR [rdi+88]
	and r8, r13
	mov QWORD PTR [rdi+3704], r8
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+3712], r8
	mov r8, QWORD PTR [rdi+104]
	and r8, r13
	mov QWORD PTR [rdi+3720], r8
	mov r8, QWORD PTR [rdi+3512]
	add r8, QWORD PTR [rdi+3680]
	mov QWORD PTR [rdi+3512], r8
	mov r8, QWORD PTR [rdi+3520]
	adc r8, QWORD PTR [rdi+3688]
	mov QWORD PTR [rdi+3520], r8
	mov r8, QWORD PTR [rdi+3528]
	adc r8, QWORD PTR [rdi+3696]
	mov QWORD PTR [rdi+3528], r8
	mov r8, QWORD PTR [rdi+3536]
	adc r8, QWORD PTR [rdi+3704]
	mov QWORD PTR [rdi+3536], r8
	mov r8, QWORD PTR [rdi+3544]
	adc r8, QWORD PTR [rdi+3712]
	mov QWORD PTR [rdi+3544], r8
	mov r8, QWORD PTR [rdi+3552]
	adc r8, QWORD PTR [rdi+3720]
	mov QWORD PTR [rdi+3552], r8
	mov r8, QWORD PTR [rdi+3560]
	adc r8, QWORD PTR [rdi+3728]
	mov QWORD PTR [rdi+3560], r8
	mov r13, -1
	mov r8, QWORD PTR [rdi+64]
	and r8, r13
	mov QWORD PTR [rdi+3680], r8
	mov r8, QWORD PTR [rdi+72]
	and r8, r13
	mov QWORD PTR [rdi+3688], r8
	mov r8, QWORD PTR [rdi+80]
	and r8, r13
	mov QWORD PTR [rdi+3696], r8
	mov r8, QWORD PTR [rdi+88]
	and r8, r13
	mov QWORD PTR [rdi+3704], r8
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+3712], r8
	mov r8, QWORD PTR [rdi+104]
	and r8, r13
	mov QWORD PTR [rdi+3720], r8
	mov r8, QWORD PTR [rdi+3512]
	sub r8, QWORD PTR [rdi+3680]
	mov QWORD PTR [rdi+3512], r8
	mov r8, QWORD PTR [rdi+3520]
	sbb r8, QWORD PTR [rdi+3688]
	mov QWORD PTR [rdi+3520], r8
	mov r8, QWORD PTR [rdi+3528]
	sbb r8, QWORD PTR [rdi+3696]
	mov QWORD PTR [rdi+3528], r8
	mov r8, QWORD PTR [rdi+3536]
	sbb r8, QWORD PTR [rdi+3704]
	mov QWORD PTR [rdi+3536], r8
	mov r8, QWORD PTR [rdi+3544]
	sbb r8, QWORD PTR [rdi+3712]
	mov QWORD PTR [rdi+3544], r8
	mov r8, QWORD PTR [rdi+3552]
	sbb r8, QWORD PTR [rdi+3720]
	mov QWORD PTR [rdi+3552], r8
	mov r8, QWORD PTR [rdi+3560]
	sbb r8, QWORD PTR [rdi+3728]
	mov QWORD PTR [rdi+3560], r8
	mov rdx, QWORD PTR [rdi+3560]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+64]
	and r8, r13
	mov QWORD PTR [rdi+3680], r8
	mov r8, QWORD PTR [rdi+72]
	and r8, r13
	mov QWORD PTR [rdi+3688], r8
	mov r8, QWORD PTR [rdi+80]
	and r8, r13
	mov QWORD PTR [rdi+3696], r8
	mov r8, QWORD PTR [rdi+88]
	and r8, r13
	mov QWORD PTR [rdi+3704], r8
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+3712], r8
	mov r8, QWORD PTR [rdi+104]
	and r8, r13
	mov QWORD PTR [rdi+3720], r8
	mov r8, QWORD PTR [rdi+3512]
	add r8, QWORD PTR [rdi+3680]
	mov QWORD PTR [rdi+3512], r8
	mov r8, QWORD PTR [rdi+3520]
	adc r8, QWORD PTR [rdi+3688]
	mov QWORD PTR [rdi+3520], r8
	mov r8, QWORD PTR [rdi+3528]
	adc r8, QWORD PTR [rdi+3696]
	mov QWORD PTR [rdi+3528], r8
	mov r8, QWORD PTR [rdi+3536]
	adc r8, QWORD PTR [rdi+3704]
	mov QWORD PTR [rdi+3536], r8
	mov r8, QWORD PTR [rdi+3544]
	adc r8, QWORD PTR [rdi+3712]
	mov QWORD PTR [rdi+3544], r8
	mov r8, QWORD PTR [rdi+3552]
	adc r8, QWORD PTR [rdi+3720]
	mov QWORD PTR [rdi+3552], r8
	mov r8, QWORD PTR [rdi+3560]
	adc r8, QWORD PTR [rdi+3728]
	mov QWORD PTR [rdi+3560], r8
	mov rdx, QWORD PTR [rdi+3400]
	mov rcx, rdx
	shr rcx, 63
	mov eax, 0
	sub rax, rcx
	mov rcx, rax
	movabs rax, 4294973439
	movabs rdx, -6144
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3624], rax
	movabs rax, -8800387991552
	movabs rdx, 8796093024255
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3632], rax
	movabs rax, 52776558151678
	movabs rdx, -52776558151680
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3640], rax
	movabs rax, -26388279070720
	movabs rdx, 26388279070719
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3648], rax
	movabs rax, 26388279078911
	movabs rdx, -26388279078912
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3656], rax
	movabs rax, -17592186050560
	movabs rdx, 17592186050559
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3664], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+3512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3624]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3632]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3640]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3648]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3656]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3664]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+3520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3624]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3632]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3640]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3648]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3656]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3664]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+3528]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3624]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3632]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3640]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3648]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3656]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3664]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+3536]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3624]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3632]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3640]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3648]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3656]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3664]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+3544]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3624]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3632]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3640]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3648]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3656]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3664]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+3552]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3624]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3632]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3640]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3648]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3656]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3664]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1456], r14
	mov QWORD PTR [rdi+1464], r15
	mov QWORD PTR [rdi+1472], r8
	mov QWORD PTR [rdi+1480], r9
	mov QWORD PTR [rdi+1488], r10
	mov QWORD PTR [rdi+1496], r11
	mov rbx, QWORD PTR [rdi+1504]
	mov rbp, QWORD PTR [rdi+1512]
	mov r12, QWORD PTR [rdi+1520]
	mov r13, QWORD PTR [rdi+1528]
	mov r14, QWORD PTR [rdi+1536]
	mov r15, QWORD PTR [rdi+1544]
	ret
	.p2align 6
