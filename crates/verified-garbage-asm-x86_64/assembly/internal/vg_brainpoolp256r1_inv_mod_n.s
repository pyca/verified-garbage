// The functions of `src/internal/vg_brainpoolp256r1_inv_mod_n.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp256r1_inv_mod_n:
	movq xmm0, rbx
	movq xmm1, rbp
	movq xmm2, r12
	movq xmm3, r13
	movq xmm4, r14
	movq xmm5, r15
	mov ebx, 1
	mov r14d, 10
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2312], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2320], rax
	mov r8d, 0
	mov QWORD PTR [rdi+2328], r8
	mov rax, QWORD PTR [rdi+1248]
	mov QWORD PTR [rdi+2336], rax
	mov rax, QWORD PTR [rdi+1256]
	mov QWORD PTR [rdi+2344], rax
	mov rax, QWORD PTR [rdi+1264]
	mov QWORD PTR [rdi+2352], rax
	mov rax, QWORD PTR [rdi+1272]
	mov QWORD PTR [rdi+2360], rax
	mov r8d, 0
	mov QWORD PTR [rdi+2368], r8
	mov r8d, 0
	mov QWORD PTR [rdi+2376], r8
	mov QWORD PTR [rdi+2384], r8
	mov QWORD PTR [rdi+2392], r8
	mov QWORD PTR [rdi+2400], r8
	mov QWORD PTR [rdi+2408], r8
	mov r8d, 0
	mov QWORD PTR [rdi+2416], r8
	mov QWORD PTR [rdi+2424], r8
	mov QWORD PTR [rdi+2432], r8
	mov QWORD PTR [rdi+2440], r8
	mov QWORD PTR [rdi+2448], r8
	mov r8d, 1
	mov QWORD PTR [rdi+2416], r8
20:
	mov rax, QWORD PTR [rdi+2296]
	mov QWORD PTR [rdi+2536], rax
	mov rax, QWORD PTR [rdi+2336]
	mov QWORD PTR [rdi+2544], rax
	xor rbx, -1
	mov r8, QWORD PTR [rdi+2536]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+2544]
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
	mov rax, QWORD PTR [rdi+2536]
	mul r8
	mov QWORD PTR [rdi+2552], rax
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add rax, QWORD PTR [rdi+2552]
	shr rax, 15
	mov QWORD PTR [rdi+2552], rax
	mov rax, QWORD PTR [rdi+2536]
	mul r13
	mov QWORD PTR [rdi+2536], rax
	mov rax, QWORD PTR [rdi+2544]
	mul rbp
	add rax, QWORD PTR [rdi+2536]
	shr rax, 15
	mov QWORD PTR [rdi+2544], rax
	mov rax, QWORD PTR [rdi+2552]
	mov QWORD PTR [rdi+2536], rax
	mov r9, r8
	mov r10, rcx
	mov r11, r13
	mov r12, rbp
	mov r8, QWORD PTR [rdi+2536]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+2544]
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
	mov rax, QWORD PTR [rdi+2536]
	mul r8
	mov QWORD PTR [rdi+2552], rax
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add rax, QWORD PTR [rdi+2552]
	shr rax, 15
	mov QWORD PTR [rdi+2552], rax
	mov rax, QWORD PTR [rdi+2536]
	mul r13
	mov QWORD PTR [rdi+2536], rax
	mov rax, QWORD PTR [rdi+2544]
	mul rbp
	add rax, QWORD PTR [rdi+2536]
	shr rax, 15
	mov QWORD PTR [rdi+2544], rax
	mov rax, QWORD PTR [rdi+2552]
	mov QWORD PTR [rdi+2536], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+2552], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+2552]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+2552], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+2552]
	mov r12, rax
	mov r8, QWORD PTR [rdi+2536]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+2544]
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
	mov rax, QWORD PTR [rdi+2536]
	mul r8
	mov QWORD PTR [rdi+2552], rax
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add rax, QWORD PTR [rdi+2552]
	shr rax, 15
	mov QWORD PTR [rdi+2552], rax
	mov rax, QWORD PTR [rdi+2536]
	mul r13
	mov QWORD PTR [rdi+2536], rax
	mov rax, QWORD PTR [rdi+2544]
	mul rbp
	add rax, QWORD PTR [rdi+2536]
	shr rax, 15
	mov QWORD PTR [rdi+2544], rax
	mov rax, QWORD PTR [rdi+2552]
	mov QWORD PTR [rdi+2536], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+2552], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+2552]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+2552], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+2552]
	mov r12, rax
	mov r8, QWORD PTR [rdi+2536]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+2544]
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
	mov QWORD PTR [rdi+2552], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+2552]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+2552], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+2552]
	mov r12, rax
	xor rbx, -1
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+2584], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+2592], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+2584]
	mov rax, rbp
	and rax, QWORD PTR [rdi+2592]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2296]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2336]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2536], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2304]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2344]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2544], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2312]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2352]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2552], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2320]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2360]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2560], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2328]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2368]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2568], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2536]
	mov r8, QWORD PTR [rdi+2544]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdi+2544]
	mov r8, QWORD PTR [rdi+2552]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdi+2552]
	mov r8, QWORD PTR [rdi+2560]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdi+2560]
	mov r8, QWORD PTR [rdi+2568]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2480], rax
	mov rdx, QWORD PTR [rdi+2568]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2488], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+2584], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+2592], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+2584]
	mov rax, rbp
	and rax, QWORD PTR [rdi+2592]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2296]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2336]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2536], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2304]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2344]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2544], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2312]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2352]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2552], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2320]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2360]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2560], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2328]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2368]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2568], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2536]
	mov r8, QWORD PTR [rdi+2544]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdi+2544]
	mov r8, QWORD PTR [rdi+2552]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2504], rax
	mov rax, QWORD PTR [rdi+2552]
	mov r8, QWORD PTR [rdi+2560]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2512], rax
	mov rax, QWORD PTR [rdi+2560]
	mov r8, QWORD PTR [rdi+2568]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2520], rax
	mov rdx, QWORD PTR [rdi+2568]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+2528], rax
	mov rax, QWORD PTR [rdi+2456]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rdi+2464]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rdi+2472]
	mov QWORD PTR [rdi+2312], rax
	mov rax, QWORD PTR [rdi+2480]
	mov QWORD PTR [rdi+2320], rax
	mov rax, QWORD PTR [rdi+2488]
	mov QWORD PTR [rdi+2328], rax
	mov rax, QWORD PTR [rdi+2496]
	mov QWORD PTR [rdi+2336], rax
	mov rax, QWORD PTR [rdi+2504]
	mov QWORD PTR [rdi+2344], rax
	mov rax, QWORD PTR [rdi+2512]
	mov QWORD PTR [rdi+2352], rax
	mov rax, QWORD PTR [rdi+2520]
	mov QWORD PTR [rdi+2360], rax
	mov rax, QWORD PTR [rdi+2528]
	mov QWORD PTR [rdi+2368], rax
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+2584], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+2592], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+2584]
	mov rax, rbp
	and rax, QWORD PTR [rdi+2592]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2376]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2416]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2536], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2384]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2424]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2544], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2392]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2432]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2552], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2400]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2440]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2560], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2408]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2448]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2568], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2536]
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+2568]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+2576], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+2536], r8
	mov r8, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+2544], r8
	mov r8, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+2552], r8
	mov r8, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+2560], r8
	mov r8, QWORD PTR [rdi+2568]
	add r8, rbp
	mov QWORD PTR [rdi+2568], r8
	mov r8, QWORD PTR [rdi+2576]
	adc r8, 0
	mov QWORD PTR [rdi+2576], r8
	mov rax, QWORD PTR [rdi+2544]
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdi+2552]
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdi+2560]
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdi+2568]
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdi+2576]
	mov QWORD PTR [rdi+2488], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+2584], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+2592], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+2584]
	mov rax, rbp
	and rax, QWORD PTR [rdi+2592]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2376]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2416]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2536], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2384]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2424]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2544], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2392]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2432]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2552], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2400]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2440]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2560], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2408]
	xor rax, QWORD PTR [rdi+2584]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2448]
	xor rax, QWORD PTR [rdi+2592]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+2568], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2536]
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+2568]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+2576], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+2536], r8
	mov r8, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+2544], r8
	mov r8, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+2552], r8
	mov r8, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+2560], r8
	mov r8, QWORD PTR [rdi+2568]
	add r8, rbp
	mov QWORD PTR [rdi+2568], r8
	mov r8, QWORD PTR [rdi+2576]
	adc r8, 0
	mov QWORD PTR [rdi+2576], r8
	mov rax, QWORD PTR [rdi+2544]
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rdi+2552]
	mov QWORD PTR [rdi+2424], rax
	mov rax, QWORD PTR [rdi+2560]
	mov QWORD PTR [rdi+2432], rax
	mov rax, QWORD PTR [rdi+2568]
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdi+2576]
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdi+2456]
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rdi+2464]
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rdi+2472]
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rdi+2480]
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rdi+2488]
	mov QWORD PTR [rdi+2408], rax
	sub r14, 1
	jne 20b
	mov r8d, 0
	mov QWORD PTR [rdi+2528], r8
	mov rdx, QWORD PTR [rdi+2408]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+2496], r8
	mov r8, QWORD PTR [rdi+104]
	and r8, r13
	mov QWORD PTR [rdi+2504], r8
	mov r8, QWORD PTR [rdi+112]
	and r8, r13
	mov QWORD PTR [rdi+2512], r8
	mov r8, QWORD PTR [rdi+120]
	and r8, r13
	mov QWORD PTR [rdi+2520], r8
	mov r8, QWORD PTR [rdi+2376]
	add r8, QWORD PTR [rdi+2496]
	mov QWORD PTR [rdi+2376], r8
	mov r8, QWORD PTR [rdi+2384]
	adc r8, QWORD PTR [rdi+2504]
	mov QWORD PTR [rdi+2384], r8
	mov r8, QWORD PTR [rdi+2392]
	adc r8, QWORD PTR [rdi+2512]
	mov QWORD PTR [rdi+2392], r8
	mov r8, QWORD PTR [rdi+2400]
	adc r8, QWORD PTR [rdi+2520]
	mov QWORD PTR [rdi+2400], r8
	mov r8, QWORD PTR [rdi+2408]
	adc r8, QWORD PTR [rdi+2528]
	mov QWORD PTR [rdi+2408], r8
	mov r13, -1
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+2496], r8
	mov r8, QWORD PTR [rdi+104]
	and r8, r13
	mov QWORD PTR [rdi+2504], r8
	mov r8, QWORD PTR [rdi+112]
	and r8, r13
	mov QWORD PTR [rdi+2512], r8
	mov r8, QWORD PTR [rdi+120]
	and r8, r13
	mov QWORD PTR [rdi+2520], r8
	mov r8, QWORD PTR [rdi+2376]
	sub r8, QWORD PTR [rdi+2496]
	mov QWORD PTR [rdi+2376], r8
	mov r8, QWORD PTR [rdi+2384]
	sbb r8, QWORD PTR [rdi+2504]
	mov QWORD PTR [rdi+2384], r8
	mov r8, QWORD PTR [rdi+2392]
	sbb r8, QWORD PTR [rdi+2512]
	mov QWORD PTR [rdi+2392], r8
	mov r8, QWORD PTR [rdi+2400]
	sbb r8, QWORD PTR [rdi+2520]
	mov QWORD PTR [rdi+2400], r8
	mov r8, QWORD PTR [rdi+2408]
	sbb r8, QWORD PTR [rdi+2528]
	mov QWORD PTR [rdi+2408], r8
	mov rdx, QWORD PTR [rdi+2408]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+2496], r8
	mov r8, QWORD PTR [rdi+104]
	and r8, r13
	mov QWORD PTR [rdi+2504], r8
	mov r8, QWORD PTR [rdi+112]
	and r8, r13
	mov QWORD PTR [rdi+2512], r8
	mov r8, QWORD PTR [rdi+120]
	and r8, r13
	mov QWORD PTR [rdi+2520], r8
	mov r8, QWORD PTR [rdi+2376]
	add r8, QWORD PTR [rdi+2496]
	mov QWORD PTR [rdi+2376], r8
	mov r8, QWORD PTR [rdi+2384]
	adc r8, QWORD PTR [rdi+2504]
	mov QWORD PTR [rdi+2384], r8
	mov r8, QWORD PTR [rdi+2392]
	adc r8, QWORD PTR [rdi+2512]
	mov QWORD PTR [rdi+2392], r8
	mov r8, QWORD PTR [rdi+2400]
	adc r8, QWORD PTR [rdi+2520]
	mov QWORD PTR [rdi+2400], r8
	mov r8, QWORD PTR [rdi+2408]
	adc r8, QWORD PTR [rdi+2528]
	mov QWORD PTR [rdi+2408], r8
	mov rdx, QWORD PTR [rdi+2296]
	mov rcx, rdx
	shr rcx, 63
	mov eax, 0
	sub rax, rcx
	mov rcx, rax
	movabs rax, 6341486884500568907
	movabs rdx, 4043266860309011292
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2456], rax
	movabs rax, 8411507225186356989
	movabs rdx, 1692734857337395194
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2464], rax
	movabs rax, 1122810836063238529
	movabs rdx, 3373482058146993136
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2472], rax
	movabs rax, -6411451936213087449
	movabs rdx, 213188074893958805
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2480], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+2376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2456]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2464]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2472]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2480]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rcx, QWORD PTR [rdi+2384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2456]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2464]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2472]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2480]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2456]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2464]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2472]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2480]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2456]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2464]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2472]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2480]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -288302128752750871
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
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
	mov QWORD PTR [rdi+992], r12
	mov QWORD PTR [rdi+1000], r13
	mov QWORD PTR [rdi+1008], r8
	mov QWORD PTR [rdi+1016], r9
	movq rbx, xmm0
	movq rbp, xmm1
	movq r12, xmm2
	movq r13, xmm3
	movq r14, xmm4
	movq r15, xmm5
	ret
	.p2align 6
