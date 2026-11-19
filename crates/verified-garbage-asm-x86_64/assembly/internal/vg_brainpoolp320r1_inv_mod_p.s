// The functions of `src/internal/vg_brainpoolp320r1_inv_mod_p.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_inv_mod_p:
	movq xmm0, rbx
	movq xmm1, rbp
	movq xmm2, r12
	movq xmm3, r13
	movq xmm4, r14
	movq xmm5, r15
	mov ebx, 1
	mov r14d, 15
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2848], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2856], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2864], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2872], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2880], rax
	mov r8d, 0
	mov QWORD PTR [rdi+2888], r8
	mov rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+2896], rax
	mov rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+2904], rax
	mov rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+2912], rax
	mov rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+2920], rax
	mov rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+2928], rax
	mov r8d, 0
	mov QWORD PTR [rdi+2936], r8
	mov r8d, 0
	mov QWORD PTR [rdi+2944], r8
	mov QWORD PTR [rdi+2952], r8
	mov QWORD PTR [rdi+2960], r8
	mov QWORD PTR [rdi+2968], r8
	mov QWORD PTR [rdi+2976], r8
	mov QWORD PTR [rdi+2984], r8
	mov r8d, 0
	mov QWORD PTR [rdi+2992], r8
	mov QWORD PTR [rdi+3000], r8
	mov QWORD PTR [rdi+3008], r8
	mov QWORD PTR [rdi+3016], r8
	mov QWORD PTR [rdi+3024], r8
	mov QWORD PTR [rdi+3032], r8
	mov r8d, 1
	mov QWORD PTR [rdi+2992], r8
20:
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+2896]
	mov QWORD PTR [rdi+3144], rax
	xor rbx, -1
	mov r8, QWORD PTR [rdi+3136]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+3144]
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
	mov rax, QWORD PTR [rdi+3136]
	mul r8
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+3144]
	mul rcx
	add rax, QWORD PTR [rdi+3152]
	shr rax, 15
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+3136]
	mul r13
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+3144]
	mul rbp
	add rax, QWORD PTR [rdi+3136]
	shr rax, 15
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+3136], rax
	mov r9, r8
	mov r10, rcx
	mov r11, r13
	mov r12, rbp
	mov r8, QWORD PTR [rdi+3136]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+3144]
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
	mov rax, QWORD PTR [rdi+3136]
	mul r8
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+3144]
	mul rcx
	add rax, QWORD PTR [rdi+3152]
	shr rax, 15
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+3136]
	mul r13
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+3144]
	mul rbp
	add rax, QWORD PTR [rdi+3136]
	shr rax, 15
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+3136], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+3152], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+3152]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+3152], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+3152]
	mov r12, rax
	mov r8, QWORD PTR [rdi+3136]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+3144]
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
	mov rax, QWORD PTR [rdi+3136]
	mul r8
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+3144]
	mul rcx
	add rax, QWORD PTR [rdi+3152]
	shr rax, 15
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+3136]
	mul r13
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+3144]
	mul rbp
	add rax, QWORD PTR [rdi+3136]
	shr rax, 15
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+3136], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+3152], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+3152]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+3152], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+3152]
	mov r12, rax
	mov r8, QWORD PTR [rdi+3136]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+3144]
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
	mov QWORD PTR [rdi+3152], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+3152]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+3152], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+3152]
	mov r12, rax
	xor rbx, -1
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3192], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3200], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+3192]
	mov rax, rbp
	and rax, QWORD PTR [rdi+3200]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2848]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2896]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3136], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2856]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2904]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3144], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2864]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2912]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3152], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2872]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2920]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3160], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2880]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2928]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3168], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2888]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2936]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3176], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3136]
	mov r8, QWORD PTR [rdi+3144]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3040], rax
	mov rax, QWORD PTR [rdi+3144]
	mov r8, QWORD PTR [rdi+3152]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3048], rax
	mov rax, QWORD PTR [rdi+3152]
	mov r8, QWORD PTR [rdi+3160]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3056], rax
	mov rax, QWORD PTR [rdi+3160]
	mov r8, QWORD PTR [rdi+3168]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3064], rax
	mov rax, QWORD PTR [rdi+3168]
	mov r8, QWORD PTR [rdi+3176]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3072], rax
	mov rdx, QWORD PTR [rdi+3176]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3080], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3192], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3200], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+3192]
	mov rax, rbp
	and rax, QWORD PTR [rdi+3200]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2848]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2896]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3136], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2856]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2904]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3144], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2864]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2912]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3152], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2872]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2920]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3160], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2880]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2928]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3168], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2888]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2936]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3176], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3136]
	mov r8, QWORD PTR [rdi+3144]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+3144]
	mov r8, QWORD PTR [rdi+3152]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+3152]
	mov r8, QWORD PTR [rdi+3160]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+3160]
	mov r8, QWORD PTR [rdi+3168]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+3168]
	mov r8, QWORD PTR [rdi+3176]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3120], rax
	mov rdx, QWORD PTR [rdi+3176]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+3040]
	mov QWORD PTR [rdi+2848], rax
	mov rax, QWORD PTR [rdi+3048]
	mov QWORD PTR [rdi+2856], rax
	mov rax, QWORD PTR [rdi+3056]
	mov QWORD PTR [rdi+2864], rax
	mov rax, QWORD PTR [rdi+3064]
	mov QWORD PTR [rdi+2872], rax
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi+2880], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+2888], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+2896], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+2904], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+2912], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+2920], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+2928], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+2936], rax
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3192], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3200], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+3192]
	mov rax, rbp
	and rax, QWORD PTR [rdi+3200]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2944]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2992]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3136], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2952]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3000]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3144], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2960]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3008]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3152], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2968]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3016]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3160], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2976]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3024]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3168], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2984]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3032]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3176], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3136]
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+3176]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+3184], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3136], r8
	mov r8, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3144], r8
	mov r8, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3152], r8
	mov r8, QWORD PTR [rdi+3160]
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3160], r8
	mov r8, QWORD PTR [rdi+3168]
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3168], r8
	mov r8, QWORD PTR [rdi+3176]
	add r8, rbp
	mov QWORD PTR [rdi+3176], r8
	mov r8, QWORD PTR [rdi+3184]
	adc r8, 0
	mov QWORD PTR [rdi+3184], r8
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+3040], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+3048], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+3056], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+3064], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+3080], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3192], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+3200], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+3192]
	mov rax, rbp
	and rax, QWORD PTR [rdi+3200]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2944]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+2992]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3136], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2952]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3000]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3144], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2960]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3008]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3152], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2968]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3016]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3160], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2976]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3024]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3168], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+2984]
	xor rax, QWORD PTR [rdi+3192]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+3032]
	xor rax, QWORD PTR [rdi+3200]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+3176], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+3136]
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+3176]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+3184], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+3136]
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3136], r8
	mov r8, QWORD PTR [rdi+3144]
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3144], r8
	mov r8, QWORD PTR [rdi+3152]
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3152], r8
	mov r8, QWORD PTR [rdi+3160]
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3160], r8
	mov r8, QWORD PTR [rdi+3168]
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+3168], r8
	mov r8, QWORD PTR [rdi+3176]
	add r8, rbp
	mov QWORD PTR [rdi+3176], r8
	mov r8, QWORD PTR [rdi+3184]
	adc r8, 0
	mov QWORD PTR [rdi+3184], r8
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+2992], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+3000], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+3008], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+3016], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+3024], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+3032], rax
	mov rax, QWORD PTR [rdi+3040]
	mov QWORD PTR [rdi+2944], rax
	mov rax, QWORD PTR [rdi+3048]
	mov QWORD PTR [rdi+2952], rax
	mov rax, QWORD PTR [rdi+3056]
	mov QWORD PTR [rdi+2960], rax
	mov rax, QWORD PTR [rdi+3064]
	mov QWORD PTR [rdi+2968], rax
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi+2976], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+2984], rax
	sub r14, 1
	jne 20b
	mov r8d, 0
	mov QWORD PTR [rdi+3128], r8
	mov rdx, QWORD PTR [rdi+2984]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+64]
	and r8, r13
	mov QWORD PTR [rdi+3088], r8
	mov r8, QWORD PTR [rdi+72]
	and r8, r13
	mov QWORD PTR [rdi+3096], r8
	mov r8, QWORD PTR [rdi+80]
	and r8, r13
	mov QWORD PTR [rdi+3104], r8
	mov r8, QWORD PTR [rdi+88]
	and r8, r13
	mov QWORD PTR [rdi+3112], r8
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+3120], r8
	mov r8, QWORD PTR [rdi+2944]
	add r8, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+2944], r8
	mov r8, QWORD PTR [rdi+2952]
	adc r8, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+2952], r8
	mov r8, QWORD PTR [rdi+2960]
	adc r8, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+2960], r8
	mov r8, QWORD PTR [rdi+2968]
	adc r8, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+2968], r8
	mov r8, QWORD PTR [rdi+2976]
	adc r8, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+2976], r8
	mov r8, QWORD PTR [rdi+2984]
	adc r8, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+2984], r8
	mov r13, -1
	mov r8, QWORD PTR [rdi+64]
	and r8, r13
	mov QWORD PTR [rdi+3088], r8
	mov r8, QWORD PTR [rdi+72]
	and r8, r13
	mov QWORD PTR [rdi+3096], r8
	mov r8, QWORD PTR [rdi+80]
	and r8, r13
	mov QWORD PTR [rdi+3104], r8
	mov r8, QWORD PTR [rdi+88]
	and r8, r13
	mov QWORD PTR [rdi+3112], r8
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+3120], r8
	mov r8, QWORD PTR [rdi+2944]
	sub r8, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+2944], r8
	mov r8, QWORD PTR [rdi+2952]
	sbb r8, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+2952], r8
	mov r8, QWORD PTR [rdi+2960]
	sbb r8, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+2960], r8
	mov r8, QWORD PTR [rdi+2968]
	sbb r8, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+2968], r8
	mov r8, QWORD PTR [rdi+2976]
	sbb r8, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+2976], r8
	mov r8, QWORD PTR [rdi+2984]
	sbb r8, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+2984], r8
	mov rdx, QWORD PTR [rdi+2984]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+64]
	and r8, r13
	mov QWORD PTR [rdi+3088], r8
	mov r8, QWORD PTR [rdi+72]
	and r8, r13
	mov QWORD PTR [rdi+3096], r8
	mov r8, QWORD PTR [rdi+80]
	and r8, r13
	mov QWORD PTR [rdi+3104], r8
	mov r8, QWORD PTR [rdi+88]
	and r8, r13
	mov QWORD PTR [rdi+3112], r8
	mov r8, QWORD PTR [rdi+96]
	and r8, r13
	mov QWORD PTR [rdi+3120], r8
	mov r8, QWORD PTR [rdi+2944]
	add r8, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+2944], r8
	mov r8, QWORD PTR [rdi+2952]
	adc r8, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+2952], r8
	mov r8, QWORD PTR [rdi+2960]
	adc r8, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+2960], r8
	mov r8, QWORD PTR [rdi+2968]
	adc r8, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+2968], r8
	mov r8, QWORD PTR [rdi+2976]
	adc r8, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+2976], r8
	mov r8, QWORD PTR [rdi+2984]
	adc r8, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+2984], r8
	mov rdx, QWORD PTR [rdi+2848]
	mov rcx, rdx
	shr rcx, 63
	mov eax, 0
	sub rax, rcx
	mov rcx, rax
	movabs rax, -8134663496871414077
	movabs rdx, 7906126371255924580
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3040], rax
	movabs rax, -3452307168264574326
	movabs rdx, 9186156869147017630
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3048], rax
	movabs rax, -6581371097328726452
	movabs rdx, 6117447176747564962
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3056], rax
	movabs rax, 5847642496647793751
	movabs rdx, -8064407064575323122
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3064], rax
	movabs rax, 4938540567928630852
	movabs rdx, -8154595448141749901
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+3072], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+2944]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3040]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3048]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3056]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3064]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3072]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+2952]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3040]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3048]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3056]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3064]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3072]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3040]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3048]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3056]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3064]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3072]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3040]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3048]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3056]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3064]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3072]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+3040]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3048]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3056]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3064]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+3072]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1224], r13
	mov QWORD PTR [rdi+1232], r14
	mov QWORD PTR [rdi+1240], r8
	mov QWORD PTR [rdi+1248], r9
	mov QWORD PTR [rdi+1256], r10
	movq rbx, xmm0
	movq rbp, xmm1
	movq r12, xmm2
	movq r13, xmm3
	movq r14, xmm4
	movq r15, xmm5
	ret
	.p2align 6
