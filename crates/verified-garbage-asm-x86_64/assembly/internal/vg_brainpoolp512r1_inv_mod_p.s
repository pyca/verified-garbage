// The functions of `src/internal/vg_brainpoolp512r1_inv_mod_p.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_inv_mod_p:
	mov QWORD PTR [rdi+1984], rbx
	mov QWORD PTR [rdi+1992], rbp
	mov QWORD PTR [rdi+2000], r12
	mov QWORD PTR [rdi+2008], r13
	mov QWORD PTR [rdi+2016], r14
	mov QWORD PTR [rdi+2024], r15
	mov ebx, 1
	mov r14d, 23
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4504], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4512], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4520], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4528], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4536], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4544], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4552], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4560], rax
	mov r8d, 0
	mov QWORD PTR [rdi+4568], r8
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+4576], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+4584], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+4592], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+4600], rax
	mov rax, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+4608], rax
	mov rax, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+4616], rax
	mov rax, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+4624], rax
	mov rax, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+4632], rax
	mov r8d, 0
	mov QWORD PTR [rdi+4640], r8
	mov r8d, 0
	mov QWORD PTR [rdi+4648], r8
	mov QWORD PTR [rdi+4656], r8
	mov QWORD PTR [rdi+4664], r8
	mov QWORD PTR [rdi+4672], r8
	mov QWORD PTR [rdi+4680], r8
	mov QWORD PTR [rdi+4688], r8
	mov QWORD PTR [rdi+4696], r8
	mov QWORD PTR [rdi+4704], r8
	mov QWORD PTR [rdi+4712], r8
	mov r8d, 0
	mov QWORD PTR [rdi+4720], r8
	mov QWORD PTR [rdi+4728], r8
	mov QWORD PTR [rdi+4736], r8
	mov QWORD PTR [rdi+4744], r8
	mov QWORD PTR [rdi+4752], r8
	mov QWORD PTR [rdi+4760], r8
	mov QWORD PTR [rdi+4768], r8
	mov QWORD PTR [rdi+4776], r8
	mov QWORD PTR [rdi+4784], r8
	mov r8d, 1
	mov QWORD PTR [rdi+4720], r8
20:
	mov rax, QWORD PTR [rdi+4504]
	mov QWORD PTR [rdi+4936], rax
	mov rax, QWORD PTR [rdi+4576]
	mov QWORD PTR [rdi+4944], rax
	xor rbx, -1
	mov r8, QWORD PTR [rdi+4936]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+4944]
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
	mov rax, QWORD PTR [rdi+4936]
	mul r8
	mov QWORD PTR [rdi+4952], rax
	mov rax, QWORD PTR [rdi+4944]
	mul rcx
	add rax, QWORD PTR [rdi+4952]
	shr rax, 15
	mov QWORD PTR [rdi+4952], rax
	mov rax, QWORD PTR [rdi+4936]
	mul r13
	mov QWORD PTR [rdi+4936], rax
	mov rax, QWORD PTR [rdi+4944]
	mul rbp
	add rax, QWORD PTR [rdi+4936]
	shr rax, 15
	mov QWORD PTR [rdi+4944], rax
	mov rax, QWORD PTR [rdi+4952]
	mov QWORD PTR [rdi+4936], rax
	mov r9, r8
	mov r10, rcx
	mov r11, r13
	mov r12, rbp
	mov r8, QWORD PTR [rdi+4936]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+4944]
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
	mov rax, QWORD PTR [rdi+4936]
	mul r8
	mov QWORD PTR [rdi+4952], rax
	mov rax, QWORD PTR [rdi+4944]
	mul rcx
	add rax, QWORD PTR [rdi+4952]
	shr rax, 15
	mov QWORD PTR [rdi+4952], rax
	mov rax, QWORD PTR [rdi+4936]
	mul r13
	mov QWORD PTR [rdi+4936], rax
	mov rax, QWORD PTR [rdi+4944]
	mul rbp
	add rax, QWORD PTR [rdi+4936]
	shr rax, 15
	mov QWORD PTR [rdi+4944], rax
	mov rax, QWORD PTR [rdi+4952]
	mov QWORD PTR [rdi+4936], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+4952], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+4952]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+4952], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+4952]
	mov r12, rax
	mov r8, QWORD PTR [rdi+4936]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+4944]
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
	mov rax, QWORD PTR [rdi+4936]
	mul r8
	mov QWORD PTR [rdi+4952], rax
	mov rax, QWORD PTR [rdi+4944]
	mul rcx
	add rax, QWORD PTR [rdi+4952]
	shr rax, 15
	mov QWORD PTR [rdi+4952], rax
	mov rax, QWORD PTR [rdi+4936]
	mul r13
	mov QWORD PTR [rdi+4936], rax
	mov rax, QWORD PTR [rdi+4944]
	mul rbp
	add rax, QWORD PTR [rdi+4936]
	shr rax, 15
	mov QWORD PTR [rdi+4944], rax
	mov rax, QWORD PTR [rdi+4952]
	mov QWORD PTR [rdi+4936], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+4952], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+4952]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+4952], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+4952]
	mov r12, rax
	mov r8, QWORD PTR [rdi+4936]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+4944]
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
	mov QWORD PTR [rdi+4952], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+4952]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+4952], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+4952]
	mov r12, rax
	xor rbx, -1
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5016], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5024], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+5016]
	mov rax, rbp
	and rax, QWORD PTR [rdi+5024]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4504]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4576]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4936], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4512]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4584]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4944], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4520]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4592]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4952], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4528]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4600]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4960], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4536]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4608]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4968], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4544]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4616]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4976], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4552]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4624]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4984], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4560]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4632]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4992], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4568]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4640]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5000], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4936]
	mov r8, QWORD PTR [rdi+4944]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4792], rax
	mov rax, QWORD PTR [rdi+4944]
	mov r8, QWORD PTR [rdi+4952]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4800], rax
	mov rax, QWORD PTR [rdi+4952]
	mov r8, QWORD PTR [rdi+4960]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4808], rax
	mov rax, QWORD PTR [rdi+4960]
	mov r8, QWORD PTR [rdi+4968]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4816], rax
	mov rax, QWORD PTR [rdi+4968]
	mov r8, QWORD PTR [rdi+4976]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4824], rax
	mov rax, QWORD PTR [rdi+4976]
	mov r8, QWORD PTR [rdi+4984]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4832], rax
	mov rax, QWORD PTR [rdi+4984]
	mov r8, QWORD PTR [rdi+4992]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4840], rax
	mov rax, QWORD PTR [rdi+4992]
	mov r8, QWORD PTR [rdi+5000]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4848], rax
	mov rdx, QWORD PTR [rdi+5000]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4856], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5016], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5024], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+5016]
	mov rax, rbp
	and rax, QWORD PTR [rdi+5024]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4504]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4576]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4936], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4512]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4584]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4944], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4520]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4592]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4952], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4528]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4600]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4960], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4536]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4608]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4968], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4544]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4616]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4976], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4552]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4624]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4984], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4560]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4632]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4992], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4568]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4640]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5000], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4936]
	mov r8, QWORD PTR [rdi+4944]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4864], rax
	mov rax, QWORD PTR [rdi+4944]
	mov r8, QWORD PTR [rdi+4952]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4872], rax
	mov rax, QWORD PTR [rdi+4952]
	mov r8, QWORD PTR [rdi+4960]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4880], rax
	mov rax, QWORD PTR [rdi+4960]
	mov r8, QWORD PTR [rdi+4968]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4888], rax
	mov rax, QWORD PTR [rdi+4968]
	mov r8, QWORD PTR [rdi+4976]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4896], rax
	mov rax, QWORD PTR [rdi+4976]
	mov r8, QWORD PTR [rdi+4984]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4904], rax
	mov rax, QWORD PTR [rdi+4984]
	mov r8, QWORD PTR [rdi+4992]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4912], rax
	mov rax, QWORD PTR [rdi+4992]
	mov r8, QWORD PTR [rdi+5000]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4920], rax
	mov rdx, QWORD PTR [rdi+5000]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+4928], rax
	mov rax, QWORD PTR [rdi+4792]
	mov QWORD PTR [rdi+4504], rax
	mov rax, QWORD PTR [rdi+4800]
	mov QWORD PTR [rdi+4512], rax
	mov rax, QWORD PTR [rdi+4808]
	mov QWORD PTR [rdi+4520], rax
	mov rax, QWORD PTR [rdi+4816]
	mov QWORD PTR [rdi+4528], rax
	mov rax, QWORD PTR [rdi+4824]
	mov QWORD PTR [rdi+4536], rax
	mov rax, QWORD PTR [rdi+4832]
	mov QWORD PTR [rdi+4544], rax
	mov rax, QWORD PTR [rdi+4840]
	mov QWORD PTR [rdi+4552], rax
	mov rax, QWORD PTR [rdi+4848]
	mov QWORD PTR [rdi+4560], rax
	mov rax, QWORD PTR [rdi+4856]
	mov QWORD PTR [rdi+4568], rax
	mov rax, QWORD PTR [rdi+4864]
	mov QWORD PTR [rdi+4576], rax
	mov rax, QWORD PTR [rdi+4872]
	mov QWORD PTR [rdi+4584], rax
	mov rax, QWORD PTR [rdi+4880]
	mov QWORD PTR [rdi+4592], rax
	mov rax, QWORD PTR [rdi+4888]
	mov QWORD PTR [rdi+4600], rax
	mov rax, QWORD PTR [rdi+4896]
	mov QWORD PTR [rdi+4608], rax
	mov rax, QWORD PTR [rdi+4904]
	mov QWORD PTR [rdi+4616], rax
	mov rax, QWORD PTR [rdi+4912]
	mov QWORD PTR [rdi+4624], rax
	mov rax, QWORD PTR [rdi+4920]
	mov QWORD PTR [rdi+4632], rax
	mov rax, QWORD PTR [rdi+4928]
	mov QWORD PTR [rdi+4640], rax
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5016], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5024], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+5016]
	mov rax, rbp
	and rax, QWORD PTR [rdi+5024]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4648]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4720]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4936], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4656]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4728]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4944], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4664]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4736]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4952], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4672]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4744]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4960], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4680]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4752]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4968], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4688]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4760]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4976], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4696]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4768]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4984], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4704]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4776]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4992], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4712]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4784]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5000], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4936]
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+5000]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+5008], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+4936]
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4936], r8
	mov r8, QWORD PTR [rdi+4944]
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4944], r8
	mov r8, QWORD PTR [rdi+4952]
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4952], r8
	mov r8, QWORD PTR [rdi+4960]
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4960], r8
	mov r8, QWORD PTR [rdi+4968]
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4968], r8
	mov r8, QWORD PTR [rdi+4976]
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4976], r8
	mov r8, QWORD PTR [rdi+4984]
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4984], r8
	mov r8, QWORD PTR [rdi+4992]
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4992], r8
	mov r8, QWORD PTR [rdi+5000]
	add r8, rbp
	mov QWORD PTR [rdi+5000], r8
	mov r8, QWORD PTR [rdi+5008]
	adc r8, 0
	mov QWORD PTR [rdi+5008], r8
	mov rax, QWORD PTR [rdi+4944]
	mov QWORD PTR [rdi+4792], rax
	mov rax, QWORD PTR [rdi+4952]
	mov QWORD PTR [rdi+4800], rax
	mov rax, QWORD PTR [rdi+4960]
	mov QWORD PTR [rdi+4808], rax
	mov rax, QWORD PTR [rdi+4968]
	mov QWORD PTR [rdi+4816], rax
	mov rax, QWORD PTR [rdi+4976]
	mov QWORD PTR [rdi+4824], rax
	mov rax, QWORD PTR [rdi+4984]
	mov QWORD PTR [rdi+4832], rax
	mov rax, QWORD PTR [rdi+4992]
	mov QWORD PTR [rdi+4840], rax
	mov rax, QWORD PTR [rdi+5000]
	mov QWORD PTR [rdi+4848], rax
	mov rax, QWORD PTR [rdi+5008]
	mov QWORD PTR [rdi+4856], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5016], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5024], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+5016]
	mov rax, rbp
	and rax, QWORD PTR [rdi+5024]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4648]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4720]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4936], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4656]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4728]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4944], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4664]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4736]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4952], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4672]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4744]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4960], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4680]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4752]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4968], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4688]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4760]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4976], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4696]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4768]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4984], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4704]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4776]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+4992], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4712]
	xor rax, QWORD PTR [rdi+5016]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+4784]
	xor rax, QWORD PTR [rdi+5024]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5000], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+4936]
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+5000]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+5008], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+4936]
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4936], r8
	mov r8, QWORD PTR [rdi+4944]
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4944], r8
	mov r8, QWORD PTR [rdi+4952]
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4952], r8
	mov r8, QWORD PTR [rdi+4960]
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4960], r8
	mov r8, QWORD PTR [rdi+4968]
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4968], r8
	mov r8, QWORD PTR [rdi+4976]
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4976], r8
	mov r8, QWORD PTR [rdi+4984]
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4984], r8
	mov r8, QWORD PTR [rdi+4992]
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+4992], r8
	mov r8, QWORD PTR [rdi+5000]
	add r8, rbp
	mov QWORD PTR [rdi+5000], r8
	mov r8, QWORD PTR [rdi+5008]
	adc r8, 0
	mov QWORD PTR [rdi+5008], r8
	mov rax, QWORD PTR [rdi+4944]
	mov QWORD PTR [rdi+4720], rax
	mov rax, QWORD PTR [rdi+4952]
	mov QWORD PTR [rdi+4728], rax
	mov rax, QWORD PTR [rdi+4960]
	mov QWORD PTR [rdi+4736], rax
	mov rax, QWORD PTR [rdi+4968]
	mov QWORD PTR [rdi+4744], rax
	mov rax, QWORD PTR [rdi+4976]
	mov QWORD PTR [rdi+4752], rax
	mov rax, QWORD PTR [rdi+4984]
	mov QWORD PTR [rdi+4760], rax
	mov rax, QWORD PTR [rdi+4992]
	mov QWORD PTR [rdi+4768], rax
	mov rax, QWORD PTR [rdi+5000]
	mov QWORD PTR [rdi+4776], rax
	mov rax, QWORD PTR [rdi+5008]
	mov QWORD PTR [rdi+4784], rax
	mov rax, QWORD PTR [rdi+4792]
	mov QWORD PTR [rdi+4648], rax
	mov rax, QWORD PTR [rdi+4800]
	mov QWORD PTR [rdi+4656], rax
	mov rax, QWORD PTR [rdi+4808]
	mov QWORD PTR [rdi+4664], rax
	mov rax, QWORD PTR [rdi+4816]
	mov QWORD PTR [rdi+4672], rax
	mov rax, QWORD PTR [rdi+4824]
	mov QWORD PTR [rdi+4680], rax
	mov rax, QWORD PTR [rdi+4832]
	mov QWORD PTR [rdi+4688], rax
	mov rax, QWORD PTR [rdi+4840]
	mov QWORD PTR [rdi+4696], rax
	mov rax, QWORD PTR [rdi+4848]
	mov QWORD PTR [rdi+4704], rax
	mov rax, QWORD PTR [rdi+4856]
	mov QWORD PTR [rdi+4712], rax
	sub r14, 1
	jne 20b
	mov r8d, 0
	mov QWORD PTR [rdi+4928], r8
	mov rdx, QWORD PTR [rdi+4712]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+64]
	and r8, r13
	mov QWORD PTR [rdi+4864], r8
	mov r8, QWORD PTR [rdi+72]
	and r8, r13
	mov QWORD PTR [rdi+4872], r8
	mov r8, QWORD PTR [rdi+80]
	and r8, r13
	mov QWORD PTR [rdi+4880], r8
	mov r8, QWORD PTR [rdi+88]
	and r8, r13
	mov QWORD PTR [rdi+4888], r8
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+4896], r8
	mov r8, QWORD PTR [rdi+104]
	and r8, r13
	mov QWORD PTR [rdi+4904], r8
	mov r8, QWORD PTR [rdi+112]
	and r8, r13
	mov QWORD PTR [rdi+4912], r8
	mov r8, QWORD PTR [rdi+120]
	and r8, r13
	mov QWORD PTR [rdi+4920], r8
	mov r8, QWORD PTR [rdi+4648]
	add r8, QWORD PTR [rdi+4864]
	mov QWORD PTR [rdi+4648], r8
	mov r8, QWORD PTR [rdi+4656]
	adc r8, QWORD PTR [rdi+4872]
	mov QWORD PTR [rdi+4656], r8
	mov r8, QWORD PTR [rdi+4664]
	adc r8, QWORD PTR [rdi+4880]
	mov QWORD PTR [rdi+4664], r8
	mov r8, QWORD PTR [rdi+4672]
	adc r8, QWORD PTR [rdi+4888]
	mov QWORD PTR [rdi+4672], r8
	mov r8, QWORD PTR [rdi+4680]
	adc r8, QWORD PTR [rdi+4896]
	mov QWORD PTR [rdi+4680], r8
	mov r8, QWORD PTR [rdi+4688]
	adc r8, QWORD PTR [rdi+4904]
	mov QWORD PTR [rdi+4688], r8
	mov r8, QWORD PTR [rdi+4696]
	adc r8, QWORD PTR [rdi+4912]
	mov QWORD PTR [rdi+4696], r8
	mov r8, QWORD PTR [rdi+4704]
	adc r8, QWORD PTR [rdi+4920]
	mov QWORD PTR [rdi+4704], r8
	mov r8, QWORD PTR [rdi+4712]
	adc r8, QWORD PTR [rdi+4928]
	mov QWORD PTR [rdi+4712], r8
	mov r13, -1
	mov r8, QWORD PTR [rdi+64]
	and r8, r13
	mov QWORD PTR [rdi+4864], r8
	mov r8, QWORD PTR [rdi+72]
	and r8, r13
	mov QWORD PTR [rdi+4872], r8
	mov r8, QWORD PTR [rdi+80]
	and r8, r13
	mov QWORD PTR [rdi+4880], r8
	mov r8, QWORD PTR [rdi+88]
	and r8, r13
	mov QWORD PTR [rdi+4888], r8
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+4896], r8
	mov r8, QWORD PTR [rdi+104]
	and r8, r13
	mov QWORD PTR [rdi+4904], r8
	mov r8, QWORD PTR [rdi+112]
	and r8, r13
	mov QWORD PTR [rdi+4912], r8
	mov r8, QWORD PTR [rdi+120]
	and r8, r13
	mov QWORD PTR [rdi+4920], r8
	mov r8, QWORD PTR [rdi+4648]
	sub r8, QWORD PTR [rdi+4864]
	mov QWORD PTR [rdi+4648], r8
	mov r8, QWORD PTR [rdi+4656]
	sbb r8, QWORD PTR [rdi+4872]
	mov QWORD PTR [rdi+4656], r8
	mov r8, QWORD PTR [rdi+4664]
	sbb r8, QWORD PTR [rdi+4880]
	mov QWORD PTR [rdi+4664], r8
	mov r8, QWORD PTR [rdi+4672]
	sbb r8, QWORD PTR [rdi+4888]
	mov QWORD PTR [rdi+4672], r8
	mov r8, QWORD PTR [rdi+4680]
	sbb r8, QWORD PTR [rdi+4896]
	mov QWORD PTR [rdi+4680], r8
	mov r8, QWORD PTR [rdi+4688]
	sbb r8, QWORD PTR [rdi+4904]
	mov QWORD PTR [rdi+4688], r8
	mov r8, QWORD PTR [rdi+4696]
	sbb r8, QWORD PTR [rdi+4912]
	mov QWORD PTR [rdi+4696], r8
	mov r8, QWORD PTR [rdi+4704]
	sbb r8, QWORD PTR [rdi+4920]
	mov QWORD PTR [rdi+4704], r8
	mov r8, QWORD PTR [rdi+4712]
	sbb r8, QWORD PTR [rdi+4928]
	mov QWORD PTR [rdi+4712], r8
	mov rdx, QWORD PTR [rdi+4712]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+64]
	and r8, r13
	mov QWORD PTR [rdi+4864], r8
	mov r8, QWORD PTR [rdi+72]
	and r8, r13
	mov QWORD PTR [rdi+4872], r8
	mov r8, QWORD PTR [rdi+80]
	and r8, r13
	mov QWORD PTR [rdi+4880], r8
	mov r8, QWORD PTR [rdi+88]
	and r8, r13
	mov QWORD PTR [rdi+4888], r8
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+4896], r8
	mov r8, QWORD PTR [rdi+104]
	and r8, r13
	mov QWORD PTR [rdi+4904], r8
	mov r8, QWORD PTR [rdi+112]
	and r8, r13
	mov QWORD PTR [rdi+4912], r8
	mov r8, QWORD PTR [rdi+120]
	and r8, r13
	mov QWORD PTR [rdi+4920], r8
	mov r8, QWORD PTR [rdi+4648]
	add r8, QWORD PTR [rdi+4864]
	mov QWORD PTR [rdi+4648], r8
	mov r8, QWORD PTR [rdi+4656]
	adc r8, QWORD PTR [rdi+4872]
	mov QWORD PTR [rdi+4656], r8
	mov r8, QWORD PTR [rdi+4664]
	adc r8, QWORD PTR [rdi+4880]
	mov QWORD PTR [rdi+4664], r8
	mov r8, QWORD PTR [rdi+4672]
	adc r8, QWORD PTR [rdi+4888]
	mov QWORD PTR [rdi+4672], r8
	mov r8, QWORD PTR [rdi+4680]
	adc r8, QWORD PTR [rdi+4896]
	mov QWORD PTR [rdi+4680], r8
	mov r8, QWORD PTR [rdi+4688]
	adc r8, QWORD PTR [rdi+4904]
	mov QWORD PTR [rdi+4688], r8
	mov r8, QWORD PTR [rdi+4696]
	adc r8, QWORD PTR [rdi+4912]
	mov QWORD PTR [rdi+4696], r8
	mov r8, QWORD PTR [rdi+4704]
	adc r8, QWORD PTR [rdi+4920]
	mov QWORD PTR [rdi+4704], r8
	mov r8, QWORD PTR [rdi+4712]
	adc r8, QWORD PTR [rdi+4928]
	mov QWORD PTR [rdi+4712], r8
	mov rdx, QWORD PTR [rdi+4504]
	mov rcx, rdx
	shr rcx, 63
	mov eax, 0
	sub rax, rcx
	mov rcx, rax
	movabs rax, 1873661326643070845
	movabs rdx, 1056599104878526838
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+4792], rax
	movabs rax, 6101285270406207851
	movabs rdx, -3182390658801324774
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+4800], rax
	movabs rax, -2679396385203987661
	movabs rdx, -3171446750050245198
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+4808], rax
	movabs rax, 2675008612587771780
	movabs rdx, 6354034642275717309
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+4816], rax
	movabs rax, 4414974772189430540
	movabs rdx, -7413355305808329371
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+4824], rax
	movabs rax, 2332672911524004617
	movabs rdx, -6138058793697063163
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+4832], rax
	movabs rax, 5731954897051614552
	movabs rdx, -1132400141731922257
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+4840], rax
	movabs rax, 2550668398727675151
	movabs rdx, -8685242098847348869
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+4848], rax
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+4792]
	mov rax, QWORD PTR [rdi+4648]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4800]
	mov rax, QWORD PTR [rdi+4648]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4792]
	mov rax, QWORD PTR [rdi+4656]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4808]
	mov rax, QWORD PTR [rdi+4648]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4800]
	mov rax, QWORD PTR [rdi+4656]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4792]
	mov rax, QWORD PTR [rdi+4664]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4816]
	mov rax, QWORD PTR [rdi+4648]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4808]
	mov rax, QWORD PTR [rdi+4656]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4800]
	mov rax, QWORD PTR [rdi+4664]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4792]
	mov rax, QWORD PTR [rdi+4672]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4824]
	mov rax, QWORD PTR [rdi+4648]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4816]
	mov rax, QWORD PTR [rdi+4656]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4808]
	mov rax, QWORD PTR [rdi+4664]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4800]
	mov rax, QWORD PTR [rdi+4672]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4792]
	mov rax, QWORD PTR [rdi+4680]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4832]
	mov rax, QWORD PTR [rdi+4648]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4824]
	mov rax, QWORD PTR [rdi+4656]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4816]
	mov rax, QWORD PTR [rdi+4664]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4808]
	mov rax, QWORD PTR [rdi+4672]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4800]
	mov rax, QWORD PTR [rdi+4680]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4792]
	mov rax, QWORD PTR [rdi+4688]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4840]
	mov rax, QWORD PTR [rdi+4648]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4832]
	mov rax, QWORD PTR [rdi+4656]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4824]
	mov rax, QWORD PTR [rdi+4664]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4816]
	mov rax, QWORD PTR [rdi+4672]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4808]
	mov rax, QWORD PTR [rdi+4680]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4800]
	mov rax, QWORD PTR [rdi+4688]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4792]
	mov rax, QWORD PTR [rdi+4696]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4848]
	mov rax, QWORD PTR [rdi+4648]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4840]
	mov rax, QWORD PTR [rdi+4656]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4832]
	mov rax, QWORD PTR [rdi+4664]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4824]
	mov rax, QWORD PTR [rdi+4672]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4816]
	mov rax, QWORD PTR [rdi+4680]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4808]
	mov rax, QWORD PTR [rdi+4688]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4800]
	mov rax, QWORD PTR [rdi+4696]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4792]
	mov rax, QWORD PTR [rdi+4704]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4848]
	mov rax, QWORD PTR [rdi+4656]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4840]
	mov rax, QWORD PTR [rdi+4664]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4832]
	mov rax, QWORD PTR [rdi+4672]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4824]
	mov rax, QWORD PTR [rdi+4680]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4816]
	mov rax, QWORD PTR [rdi+4688]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4808]
	mov rax, QWORD PTR [rdi+4696]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4800]
	mov rax, QWORD PTR [rdi+4704]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+4848]
	mov rax, QWORD PTR [rdi+4664]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4840]
	mov rax, QWORD PTR [rdi+4672]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4832]
	mov rax, QWORD PTR [rdi+4680]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4824]
	mov rax, QWORD PTR [rdi+4688]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4816]
	mov rax, QWORD PTR [rdi+4696]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4808]
	mov rax, QWORD PTR [rdi+4704]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+4848]
	mov rax, QWORD PTR [rdi+4672]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4840]
	mov rax, QWORD PTR [rdi+4680]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4832]
	mov rax, QWORD PTR [rdi+4688]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4824]
	mov rax, QWORD PTR [rdi+4696]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4816]
	mov rax, QWORD PTR [rdi+4704]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+4848]
	mov rax, QWORD PTR [rdi+4680]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4840]
	mov rax, QWORD PTR [rdi+4688]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4832]
	mov rax, QWORD PTR [rdi+4696]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4824]
	mov rax, QWORD PTR [rdi+4704]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+4848]
	mov rax, QWORD PTR [rdi+4688]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4840]
	mov rax, QWORD PTR [rdi+4696]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4832]
	mov rax, QWORD PTR [rdi+4704]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+4848]
	mov rax, QWORD PTR [rdi+4696]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4840]
	mov rax, QWORD PTR [rdi+4704]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+4848]
	mov rax, QWORD PTR [rdi+4704]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1920], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1928], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1936], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1944], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1952], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1960], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1968], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1976], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1920]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1920], rdx
	mov rdx, QWORD PTR [rdi+1928]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1928], rdx
	mov rdx, QWORD PTR [rdi+1936]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1936], rdx
	mov rdx, QWORD PTR [rdi+1944]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1944], rdx
	mov rdx, QWORD PTR [rdi+1952]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1952], rdx
	mov rdx, QWORD PTR [rdi+1960]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1960], rdx
	mov rdx, QWORD PTR [rdi+1968]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1968], rdx
	mov rdx, QWORD PTR [rdi+1976]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1976], rdx
	mov rbx, QWORD PTR [rdi+1984]
	mov rbp, QWORD PTR [rdi+1992]
	mov r12, QWORD PTR [rdi+2000]
	mov r13, QWORD PTR [rdi+2008]
	mov r14, QWORD PTR [rdi+2016]
	mov r15, QWORD PTR [rdi+2024]
	ret
	.p2align 6
