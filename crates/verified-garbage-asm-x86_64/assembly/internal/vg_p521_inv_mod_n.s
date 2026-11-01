// The functions of `src/internal/vg_p521_inv_mod_n.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_inv_mod_n:
	mov QWORD PTR [rdi+2224], rbx
	mov QWORD PTR [rdi+2232], rbp
	mov QWORD PTR [rdi+2240], r12
	mov QWORD PTR [rdi+2248], r13
	mov QWORD PTR [rdi+2256], r14
	mov QWORD PTR [rdi+2264], r15
	mov ebx, 1
	mov r14d, 23
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+5056], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+5064], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+5072], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+5080], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+5088], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+5096], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+5104], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+5112], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+5120], rax
	mov r8d, 0
	mov QWORD PTR [rdi+5128], r8
	mov rax, QWORD PTR [rdi+2728]
	mov QWORD PTR [rdi+5136], rax
	mov rax, QWORD PTR [rdi+2736]
	mov QWORD PTR [rdi+5144], rax
	mov rax, QWORD PTR [rdi+2744]
	mov QWORD PTR [rdi+5152], rax
	mov rax, QWORD PTR [rdi+2752]
	mov QWORD PTR [rdi+5160], rax
	mov rax, QWORD PTR [rdi+2760]
	mov QWORD PTR [rdi+5168], rax
	mov rax, QWORD PTR [rdi+2768]
	mov QWORD PTR [rdi+5176], rax
	mov rax, QWORD PTR [rdi+2776]
	mov QWORD PTR [rdi+5184], rax
	mov rax, QWORD PTR [rdi+2784]
	mov QWORD PTR [rdi+5192], rax
	mov rax, QWORD PTR [rdi+2792]
	mov QWORD PTR [rdi+5200], rax
	mov r8d, 0
	mov QWORD PTR [rdi+5208], r8
	mov r8d, 0
	mov QWORD PTR [rdi+5216], r8
	mov QWORD PTR [rdi+5224], r8
	mov QWORD PTR [rdi+5232], r8
	mov QWORD PTR [rdi+5240], r8
	mov QWORD PTR [rdi+5248], r8
	mov QWORD PTR [rdi+5256], r8
	mov QWORD PTR [rdi+5264], r8
	mov QWORD PTR [rdi+5272], r8
	mov QWORD PTR [rdi+5280], r8
	mov QWORD PTR [rdi+5288], r8
	mov r8d, 0
	mov QWORD PTR [rdi+5296], r8
	mov QWORD PTR [rdi+5304], r8
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r8
	mov QWORD PTR [rdi+5328], r8
	mov QWORD PTR [rdi+5336], r8
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r8
	mov QWORD PTR [rdi+5360], r8
	mov QWORD PTR [rdi+5368], r8
	mov r8d, 1
	mov QWORD PTR [rdi+5296], r8
20:
	mov rax, QWORD PTR [rdi+5056]
	mov QWORD PTR [rdi+5536], rax
	mov rax, QWORD PTR [rdi+5136]
	mov QWORD PTR [rdi+5544], rax
	xor rbx, -1
	mov r8, QWORD PTR [rdi+5536]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+5544]
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
	mov rax, QWORD PTR [rdi+5536]
	mul r8
	mov QWORD PTR [rdi+5552], rax
	mov rax, QWORD PTR [rdi+5544]
	mul rcx
	add rax, QWORD PTR [rdi+5552]
	shr rax, 15
	mov QWORD PTR [rdi+5552], rax
	mov rax, QWORD PTR [rdi+5536]
	mul r13
	mov QWORD PTR [rdi+5536], rax
	mov rax, QWORD PTR [rdi+5544]
	mul rbp
	add rax, QWORD PTR [rdi+5536]
	shr rax, 15
	mov QWORD PTR [rdi+5544], rax
	mov rax, QWORD PTR [rdi+5552]
	mov QWORD PTR [rdi+5536], rax
	mov r9, r8
	mov r10, rcx
	mov r11, r13
	mov r12, rbp
	mov r8, QWORD PTR [rdi+5536]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+5544]
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
	mov rax, QWORD PTR [rdi+5536]
	mul r8
	mov QWORD PTR [rdi+5552], rax
	mov rax, QWORD PTR [rdi+5544]
	mul rcx
	add rax, QWORD PTR [rdi+5552]
	shr rax, 15
	mov QWORD PTR [rdi+5552], rax
	mov rax, QWORD PTR [rdi+5536]
	mul r13
	mov QWORD PTR [rdi+5536], rax
	mov rax, QWORD PTR [rdi+5544]
	mul rbp
	add rax, QWORD PTR [rdi+5536]
	shr rax, 15
	mov QWORD PTR [rdi+5544], rax
	mov rax, QWORD PTR [rdi+5552]
	mov QWORD PTR [rdi+5536], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+5552], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+5552]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+5552], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+5552]
	mov r12, rax
	mov r8, QWORD PTR [rdi+5536]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+5544]
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
	mov rax, QWORD PTR [rdi+5536]
	mul r8
	mov QWORD PTR [rdi+5552], rax
	mov rax, QWORD PTR [rdi+5544]
	mul rcx
	add rax, QWORD PTR [rdi+5552]
	shr rax, 15
	mov QWORD PTR [rdi+5552], rax
	mov rax, QWORD PTR [rdi+5536]
	mul r13
	mov QWORD PTR [rdi+5536], rax
	mov rax, QWORD PTR [rdi+5544]
	mul rbp
	add rax, QWORD PTR [rdi+5536]
	shr rax, 15
	mov QWORD PTR [rdi+5544], rax
	mov rax, QWORD PTR [rdi+5552]
	mov QWORD PTR [rdi+5536], rax
	mov rax, r13
	mul r9
	mov QWORD PTR [rdi+5552], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+5552]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+5552], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+5552]
	mov r12, rax
	mov r8, QWORD PTR [rdi+5536]
	and r8, 32767
	movabs rax, 2147483648
	add r8, rax
	mov r13, QWORD PTR [rdi+5544]
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
	mov QWORD PTR [rdi+5552], rax
	mov rax, r8
	mul r9
	mov r9, rax
	mov rax, rcx
	mul r11
	add r9, rax
	mov rax, rbp
	mul r11
	add rax, QWORD PTR [rdi+5552]
	mov r11, rax
	mov rax, r13
	mul r10
	mov QWORD PTR [rdi+5552], rax
	mov rax, r8
	mul r10
	mov r10, rax
	mov rax, rcx
	mul r12
	add r10, rax
	mov rax, rbp
	mul r12
	add rax, QWORD PTR [rdi+5552]
	mov r12, rax
	xor rbx, -1
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5624], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5632], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+5624]
	mov rax, rbp
	and rax, QWORD PTR [rdi+5632]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5056]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5136]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5536], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5064]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5144]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5544], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5072]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5152]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5552], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5080]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5160]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5560], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5088]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5168]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5568], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5096]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5176]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5576], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5104]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5184]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5584], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5112]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5192]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5592], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5120]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5200]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5600], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5128]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5208]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5608], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5536]
	mov r8, QWORD PTR [rdi+5544]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+5544]
	mov r8, QWORD PTR [rdi+5552]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5384], rax
	mov rax, QWORD PTR [rdi+5552]
	mov r8, QWORD PTR [rdi+5560]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5392], rax
	mov rax, QWORD PTR [rdi+5560]
	mov r8, QWORD PTR [rdi+5568]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5400], rax
	mov rax, QWORD PTR [rdi+5568]
	mov r8, QWORD PTR [rdi+5576]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5408], rax
	mov rax, QWORD PTR [rdi+5576]
	mov r8, QWORD PTR [rdi+5584]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5416], rax
	mov rax, QWORD PTR [rdi+5584]
	mov r8, QWORD PTR [rdi+5592]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5424], rax
	mov rax, QWORD PTR [rdi+5592]
	mov r8, QWORD PTR [rdi+5600]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5432], rax
	mov rax, QWORD PTR [rdi+5600]
	mov r8, QWORD PTR [rdi+5608]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5440], rax
	mov rdx, QWORD PTR [rdi+5608]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5448], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5624], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5632], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+5624]
	mov rax, rbp
	and rax, QWORD PTR [rdi+5632]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5056]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5136]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5536], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5064]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5144]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5544], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5072]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5152]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5552], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5080]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5160]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5560], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5088]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5168]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5568], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5096]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5176]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5576], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5104]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5184]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5584], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5112]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5192]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5592], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5120]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5200]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5600], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5128]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5208]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5608], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5536]
	mov r8, QWORD PTR [rdi+5544]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5456], rax
	mov rax, QWORD PTR [rdi+5544]
	mov r8, QWORD PTR [rdi+5552]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5464], rax
	mov rax, QWORD PTR [rdi+5552]
	mov r8, QWORD PTR [rdi+5560]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5472], rax
	mov rax, QWORD PTR [rdi+5560]
	mov r8, QWORD PTR [rdi+5568]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5480], rax
	mov rax, QWORD PTR [rdi+5568]
	mov r8, QWORD PTR [rdi+5576]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5488], rax
	mov rax, QWORD PTR [rdi+5576]
	mov r8, QWORD PTR [rdi+5584]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5496], rax
	mov rax, QWORD PTR [rdi+5584]
	mov r8, QWORD PTR [rdi+5592]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5504], rax
	mov rax, QWORD PTR [rdi+5592]
	mov r8, QWORD PTR [rdi+5600]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5512], rax
	mov rax, QWORD PTR [rdi+5600]
	mov r8, QWORD PTR [rdi+5608]
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5520], rax
	mov rdx, QWORD PTR [rdi+5608]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov rax, rdx
	shr rax, 59
	shl r8, 5
	add rax, r8
	mov QWORD PTR [rdi+5528], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdi+5056], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdi+5064], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdi+5072], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdi+5080], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdi+5088], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdi+5096], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdi+5104], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdi+5112], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdi+5120], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdi+5128], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdi+5136], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdi+5144], rax
	mov rax, QWORD PTR [rdi+5472]
	mov QWORD PTR [rdi+5152], rax
	mov rax, QWORD PTR [rdi+5480]
	mov QWORD PTR [rdi+5160], rax
	mov rax, QWORD PTR [rdi+5488]
	mov QWORD PTR [rdi+5168], rax
	mov rax, QWORD PTR [rdi+5496]
	mov QWORD PTR [rdi+5176], rax
	mov rax, QWORD PTR [rdi+5504]
	mov QWORD PTR [rdi+5184], rax
	mov rax, QWORD PTR [rdi+5512]
	mov QWORD PTR [rdi+5192], rax
	mov rax, QWORD PTR [rdi+5520]
	mov QWORD PTR [rdi+5200], rax
	mov rax, QWORD PTR [rdi+5528]
	mov QWORD PTR [rdi+5208], rax
	mov rax, r9
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5624], rdx
	mov rcx, r9
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r10
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5632], rdx
	mov rbp, r10
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+5624]
	mov rax, rbp
	and rax, QWORD PTR [rdi+5632]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5216]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5296]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5536], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5224]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5304]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5544], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5232]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5312]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5552], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5240]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5320]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5560], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5248]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5328]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5568], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5256]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5336]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5576], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5264]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5344]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5584], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5272]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5352]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5592], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5280]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5360]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5600], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5288]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5368]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5608], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5536]
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+5608]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+5616], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+5536]
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5536], r8
	mov r8, QWORD PTR [rdi+5544]
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5544], r8
	mov r8, QWORD PTR [rdi+5552]
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5552], r8
	mov r8, QWORD PTR [rdi+5560]
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5560], r8
	mov r8, QWORD PTR [rdi+5568]
	mov rax, QWORD PTR [rdi+168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5568], r8
	mov r8, QWORD PTR [rdi+5576]
	mov rax, QWORD PTR [rdi+176]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5576], r8
	mov r8, QWORD PTR [rdi+5584]
	mov rax, QWORD PTR [rdi+184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5584], r8
	mov r8, QWORD PTR [rdi+5592]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5592], r8
	mov r8, QWORD PTR [rdi+5600]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5600], r8
	mov r8, QWORD PTR [rdi+5608]
	add r8, rbp
	mov QWORD PTR [rdi+5608], r8
	mov r8, QWORD PTR [rdi+5616]
	adc r8, 0
	mov QWORD PTR [rdi+5616], r8
	mov rax, QWORD PTR [rdi+5544]
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+5552]
	mov QWORD PTR [rdi+5384], rax
	mov rax, QWORD PTR [rdi+5560]
	mov QWORD PTR [rdi+5392], rax
	mov rax, QWORD PTR [rdi+5568]
	mov QWORD PTR [rdi+5400], rax
	mov rax, QWORD PTR [rdi+5576]
	mov QWORD PTR [rdi+5408], rax
	mov rax, QWORD PTR [rdi+5584]
	mov QWORD PTR [rdi+5416], rax
	mov rax, QWORD PTR [rdi+5592]
	mov QWORD PTR [rdi+5424], rax
	mov rax, QWORD PTR [rdi+5600]
	mov QWORD PTR [rdi+5432], rax
	mov rax, QWORD PTR [rdi+5608]
	mov QWORD PTR [rdi+5440], rax
	mov rax, QWORD PTR [rdi+5616]
	mov QWORD PTR [rdi+5448], rax
	mov rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5624], rdx
	mov rcx, r11
	xor rcx, rdx
	sub rcx, rdx
	mov rax, r12
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [rdi+5632], rdx
	mov rbp, r12
	xor rbp, rdx
	sub rbp, rdx
	mov r8, rcx
	and r8, QWORD PTR [rdi+5624]
	mov rax, rbp
	and rax, QWORD PTR [rdi+5632]
	add r8, rax
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5216]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5296]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5536], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5224]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5304]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5544], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5232]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5312]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5552], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5240]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5320]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5560], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5248]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5328]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5568], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5256]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5336]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5576], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5264]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5344]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5584], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5272]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5352]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5592], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5280]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5360]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5600], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5288]
	xor rax, QWORD PTR [rdi+5624]
	mul rcx
	add r8, rax
	adc r13, rdx
	mov rax, QWORD PTR [rdi+5368]
	xor rax, QWORD PTR [rdi+5632]
	mul rbp
	add r8, rax
	adc r13, rdx
	mov QWORD PTR [rdi+5608], r8
	mov r8, r13
	mov r13d, 0
	mov rax, QWORD PTR [rdi+5536]
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov rdx, QWORD PTR [rdi+5608]
	mov r8, rdx
	shr r8, 63
	mov eax, 0
	sub rax, r8
	mov r8, rax
	mov QWORD PTR [rdi+5616], r8
	mov ebp, 0
	mov r8, QWORD PTR [rdi+5536]
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5536], r8
	mov r8, QWORD PTR [rdi+5544]
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5544], r8
	mov r8, QWORD PTR [rdi+5552]
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5552], r8
	mov r8, QWORD PTR [rdi+5560]
	mov rax, QWORD PTR [rdi+160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5560], r8
	mov r8, QWORD PTR [rdi+5568]
	mov rax, QWORD PTR [rdi+168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5568], r8
	mov r8, QWORD PTR [rdi+5576]
	mov rax, QWORD PTR [rdi+176]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5576], r8
	mov r8, QWORD PTR [rdi+5584]
	mov rax, QWORD PTR [rdi+184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5584], r8
	mov r8, QWORD PTR [rdi+5592]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5592], r8
	mov r8, QWORD PTR [rdi+5600]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov QWORD PTR [rdi+5600], r8
	mov r8, QWORD PTR [rdi+5608]
	add r8, rbp
	mov QWORD PTR [rdi+5608], r8
	mov r8, QWORD PTR [rdi+5616]
	adc r8, 0
	mov QWORD PTR [rdi+5616], r8
	mov rax, QWORD PTR [rdi+5544]
	mov QWORD PTR [rdi+5296], rax
	mov rax, QWORD PTR [rdi+5552]
	mov QWORD PTR [rdi+5304], rax
	mov rax, QWORD PTR [rdi+5560]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+5568]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+5576]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+5584]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+5592]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+5600]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+5608]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+5616]
	mov QWORD PTR [rdi+5368], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdi+5216], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdi+5224], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdi+5232], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdi+5240], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdi+5248], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdi+5256], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdi+5264], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdi+5272], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdi+5280], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdi+5288], rax
	sub r14, 1
	jne 20b
	mov r8d, 0
	mov QWORD PTR [rdi+5528], r8
	mov rdx, QWORD PTR [rdi+5288]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+136]
	and r8, r13
	mov QWORD PTR [rdi+5456], r8
	mov r8, QWORD PTR [rdi+144]
	and r8, r13
	mov QWORD PTR [rdi+5464], r8
	mov r8, QWORD PTR [rdi+152]
	and r8, r13
	mov QWORD PTR [rdi+5472], r8
	mov r8, QWORD PTR [rdi+160]
	and r8, r13
	mov QWORD PTR [rdi+5480], r8
	mov r8, QWORD PTR [rdi+168]
	and r8, r13
	mov QWORD PTR [rdi+5488], r8
	mov r8, QWORD PTR [rdi+176]
	and r8, r13
	mov QWORD PTR [rdi+5496], r8
	mov r8, QWORD PTR [rdi+184]
	and r8, r13
	mov QWORD PTR [rdi+5504], r8
	mov r8, QWORD PTR [rdi+192]
	and r8, r13
	mov QWORD PTR [rdi+5512], r8
	mov r8, QWORD PTR [rdi+200]
	and r8, r13
	mov QWORD PTR [rdi+5520], r8
	mov r8, QWORD PTR [rdi+5216]
	add r8, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdi+5216], r8
	mov r8, QWORD PTR [rdi+5224]
	adc r8, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdi+5224], r8
	mov r8, QWORD PTR [rdi+5232]
	adc r8, QWORD PTR [rdi+5472]
	mov QWORD PTR [rdi+5232], r8
	mov r8, QWORD PTR [rdi+5240]
	adc r8, QWORD PTR [rdi+5480]
	mov QWORD PTR [rdi+5240], r8
	mov r8, QWORD PTR [rdi+5248]
	adc r8, QWORD PTR [rdi+5488]
	mov QWORD PTR [rdi+5248], r8
	mov r8, QWORD PTR [rdi+5256]
	adc r8, QWORD PTR [rdi+5496]
	mov QWORD PTR [rdi+5256], r8
	mov r8, QWORD PTR [rdi+5264]
	adc r8, QWORD PTR [rdi+5504]
	mov QWORD PTR [rdi+5264], r8
	mov r8, QWORD PTR [rdi+5272]
	adc r8, QWORD PTR [rdi+5512]
	mov QWORD PTR [rdi+5272], r8
	mov r8, QWORD PTR [rdi+5280]
	adc r8, QWORD PTR [rdi+5520]
	mov QWORD PTR [rdi+5280], r8
	mov r8, QWORD PTR [rdi+5288]
	adc r8, QWORD PTR [rdi+5528]
	mov QWORD PTR [rdi+5288], r8
	mov r13, -1
	mov r8, QWORD PTR [rdi+136]
	and r8, r13
	mov QWORD PTR [rdi+5456], r8
	mov r8, QWORD PTR [rdi+144]
	and r8, r13
	mov QWORD PTR [rdi+5464], r8
	mov r8, QWORD PTR [rdi+152]
	and r8, r13
	mov QWORD PTR [rdi+5472], r8
	mov r8, QWORD PTR [rdi+160]
	and r8, r13
	mov QWORD PTR [rdi+5480], r8
	mov r8, QWORD PTR [rdi+168]
	and r8, r13
	mov QWORD PTR [rdi+5488], r8
	mov r8, QWORD PTR [rdi+176]
	and r8, r13
	mov QWORD PTR [rdi+5496], r8
	mov r8, QWORD PTR [rdi+184]
	and r8, r13
	mov QWORD PTR [rdi+5504], r8
	mov r8, QWORD PTR [rdi+192]
	and r8, r13
	mov QWORD PTR [rdi+5512], r8
	mov r8, QWORD PTR [rdi+200]
	and r8, r13
	mov QWORD PTR [rdi+5520], r8
	mov r8, QWORD PTR [rdi+5216]
	sub r8, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdi+5216], r8
	mov r8, QWORD PTR [rdi+5224]
	sbb r8, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdi+5224], r8
	mov r8, QWORD PTR [rdi+5232]
	sbb r8, QWORD PTR [rdi+5472]
	mov QWORD PTR [rdi+5232], r8
	mov r8, QWORD PTR [rdi+5240]
	sbb r8, QWORD PTR [rdi+5480]
	mov QWORD PTR [rdi+5240], r8
	mov r8, QWORD PTR [rdi+5248]
	sbb r8, QWORD PTR [rdi+5488]
	mov QWORD PTR [rdi+5248], r8
	mov r8, QWORD PTR [rdi+5256]
	sbb r8, QWORD PTR [rdi+5496]
	mov QWORD PTR [rdi+5256], r8
	mov r8, QWORD PTR [rdi+5264]
	sbb r8, QWORD PTR [rdi+5504]
	mov QWORD PTR [rdi+5264], r8
	mov r8, QWORD PTR [rdi+5272]
	sbb r8, QWORD PTR [rdi+5512]
	mov QWORD PTR [rdi+5272], r8
	mov r8, QWORD PTR [rdi+5280]
	sbb r8, QWORD PTR [rdi+5520]
	mov QWORD PTR [rdi+5280], r8
	mov r8, QWORD PTR [rdi+5288]
	sbb r8, QWORD PTR [rdi+5528]
	mov QWORD PTR [rdi+5288], r8
	mov rdx, QWORD PTR [rdi+5288]
	mov r13, rdx
	shr r13, 63
	mov eax, 0
	sub rax, r13
	mov r13, rax
	mov r8, QWORD PTR [rdi+136]
	and r8, r13
	mov QWORD PTR [rdi+5456], r8
	mov r8, QWORD PTR [rdi+144]
	and r8, r13
	mov QWORD PTR [rdi+5464], r8
	mov r8, QWORD PTR [rdi+152]
	and r8, r13
	mov QWORD PTR [rdi+5472], r8
	mov r8, QWORD PTR [rdi+160]
	and r8, r13
	mov QWORD PTR [rdi+5480], r8
	mov r8, QWORD PTR [rdi+168]
	and r8, r13
	mov QWORD PTR [rdi+5488], r8
	mov r8, QWORD PTR [rdi+176]
	and r8, r13
	mov QWORD PTR [rdi+5496], r8
	mov r8, QWORD PTR [rdi+184]
	and r8, r13
	mov QWORD PTR [rdi+5504], r8
	mov r8, QWORD PTR [rdi+192]
	and r8, r13
	mov QWORD PTR [rdi+5512], r8
	mov r8, QWORD PTR [rdi+200]
	and r8, r13
	mov QWORD PTR [rdi+5520], r8
	mov r8, QWORD PTR [rdi+5216]
	add r8, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdi+5216], r8
	mov r8, QWORD PTR [rdi+5224]
	adc r8, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdi+5224], r8
	mov r8, QWORD PTR [rdi+5232]
	adc r8, QWORD PTR [rdi+5472]
	mov QWORD PTR [rdi+5232], r8
	mov r8, QWORD PTR [rdi+5240]
	adc r8, QWORD PTR [rdi+5480]
	mov QWORD PTR [rdi+5240], r8
	mov r8, QWORD PTR [rdi+5248]
	adc r8, QWORD PTR [rdi+5488]
	mov QWORD PTR [rdi+5248], r8
	mov r8, QWORD PTR [rdi+5256]
	adc r8, QWORD PTR [rdi+5496]
	mov QWORD PTR [rdi+5256], r8
	mov r8, QWORD PTR [rdi+5264]
	adc r8, QWORD PTR [rdi+5504]
	mov QWORD PTR [rdi+5264], r8
	mov r8, QWORD PTR [rdi+5272]
	adc r8, QWORD PTR [rdi+5512]
	mov QWORD PTR [rdi+5272], r8
	mov r8, QWORD PTR [rdi+5280]
	adc r8, QWORD PTR [rdi+5520]
	mov QWORD PTR [rdi+5280], r8
	mov r8, QWORD PTR [rdi+5288]
	adc r8, QWORD PTR [rdi+5528]
	mov QWORD PTR [rdi+5288], r8
	mov rdx, QWORD PTR [rdi+5056]
	mov rcx, rdx
	shr rcx, 63
	mov eax, 0
	sub rax, rcx
	mov rcx, rax
	movabs rax, 5790750135000739483
	movabs rdx, 7715465014419961198
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5376], rax
	movabs rax, -8901398257680959169
	movabs rdx, -5242779002586329489
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5384], rax
	movabs rax, 5524361809976949824
	movabs rdx, 3684374940982749583
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5392], rax
	movabs rax, 4269279581794376810
	movabs rdx, 1605252182075046401
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5400], rax
	movabs rax, -3934386676131738137
	movabs rdx, 3934386676131738131
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5408], rax
	movabs rax, -7539178563955323527
	movabs rdx, 7539178563955323526
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5416], rax
	movabs rax, -4826897450656828580
	movabs rdx, 4826897450656828579
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5424], rax
	movabs rax, 1042293571883579208
	movabs rdx, -1042293571883579209
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5432], rax
	movabs rax, 409
	movabs rdx, 102
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5440], rax
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov rax, QWORD PTR [rdi+5216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4024], rcx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov rax, QWORD PTR [rdi+5216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov rax, QWORD PTR [rdi+5224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4032], rcx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov rax, QWORD PTR [rdi+5216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov rax, QWORD PTR [rdi+5224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov rax, QWORD PTR [rdi+5232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4040], rcx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov rax, QWORD PTR [rdi+5216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov rax, QWORD PTR [rdi+5224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov rax, QWORD PTR [rdi+5232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov rax, QWORD PTR [rdi+5240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4048], rcx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov rax, QWORD PTR [rdi+5216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov rax, QWORD PTR [rdi+5224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov rax, QWORD PTR [rdi+5232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov rax, QWORD PTR [rdi+5240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov rax, QWORD PTR [rdi+5248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4056], rcx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov rax, QWORD PTR [rdi+5216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov rax, QWORD PTR [rdi+5224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov rax, QWORD PTR [rdi+5232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov rax, QWORD PTR [rdi+5240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov rax, QWORD PTR [rdi+5248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov rax, QWORD PTR [rdi+5256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4064], rcx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov rax, QWORD PTR [rdi+5216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov rax, QWORD PTR [rdi+5224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov rax, QWORD PTR [rdi+5232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov rax, QWORD PTR [rdi+5240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov rax, QWORD PTR [rdi+5248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov rax, QWORD PTR [rdi+5256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov rax, QWORD PTR [rdi+5264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4072], rcx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov rax, QWORD PTR [rdi+5216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov rax, QWORD PTR [rdi+5224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov rax, QWORD PTR [rdi+5232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov rax, QWORD PTR [rdi+5240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov rax, QWORD PTR [rdi+5248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov rax, QWORD PTR [rdi+5256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov rax, QWORD PTR [rdi+5264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov rax, QWORD PTR [rdi+5272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4080], rcx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5440]
	mov rax, QWORD PTR [rdi+5216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov rax, QWORD PTR [rdi+5224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov rax, QWORD PTR [rdi+5232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov rax, QWORD PTR [rdi+5240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov rax, QWORD PTR [rdi+5248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov rax, QWORD PTR [rdi+5256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov rax, QWORD PTR [rdi+5264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov rax, QWORD PTR [rdi+5272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov rax, QWORD PTR [rdi+5280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+200]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4088], rcx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5440]
	mov rax, QWORD PTR [rdi+5224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov rax, QWORD PTR [rdi+5232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov rax, QWORD PTR [rdi+5240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov rax, QWORD PTR [rdi+5248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov rax, QWORD PTR [rdi+5256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov rax, QWORD PTR [rdi+5264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov rax, QWORD PTR [rdi+5272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov rax, QWORD PTR [rdi+5280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+200]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+144]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5440]
	mov rax, QWORD PTR [rdi+5232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov rax, QWORD PTR [rdi+5240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov rax, QWORD PTR [rdi+5248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov rax, QWORD PTR [rdi+5256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov rax, QWORD PTR [rdi+5264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov rax, QWORD PTR [rdi+5272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov rax, QWORD PTR [rdi+5280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+200]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+152]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5440]
	mov rax, QWORD PTR [rdi+5240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov rax, QWORD PTR [rdi+5248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov rax, QWORD PTR [rdi+5256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov rax, QWORD PTR [rdi+5264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov rax, QWORD PTR [rdi+5272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov rax, QWORD PTR [rdi+5280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+200]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+160]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+5440]
	mov rax, QWORD PTR [rdi+5248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov rax, QWORD PTR [rdi+5256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov rax, QWORD PTR [rdi+5264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov rax, QWORD PTR [rdi+5272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov rax, QWORD PTR [rdi+5280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+200]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+168]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5440]
	mov rax, QWORD PTR [rdi+5256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov rax, QWORD PTR [rdi+5264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov rax, QWORD PTR [rdi+5272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov rax, QWORD PTR [rdi+5280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+200]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+176]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5440]
	mov rax, QWORD PTR [rdi+5264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov rax, QWORD PTR [rdi+5272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov rax, QWORD PTR [rdi+5280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+200]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+5440]
	mov rax, QWORD PTR [rdi+5272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov rax, QWORD PTR [rdi+5280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+200]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5440]
	mov rax, QWORD PTR [rdi+5280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+200]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+2152], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+2160], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+2168], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+2176], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+2184], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+2192], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+2200], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+2208], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+2216], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2152]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2152], rdx
	mov rdx, QWORD PTR [rdi+2160]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2160], rdx
	mov rdx, QWORD PTR [rdi+2168]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2168], rdx
	mov rdx, QWORD PTR [rdi+2176]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2176], rdx
	mov rdx, QWORD PTR [rdi+2184]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2184], rdx
	mov rdx, QWORD PTR [rdi+2192]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2192], rdx
	mov rdx, QWORD PTR [rdi+2200]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2200], rdx
	mov rdx, QWORD PTR [rdi+2208]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2208], rdx
	mov rdx, QWORD PTR [rdi+2216]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2216], rdx
	mov rbx, QWORD PTR [rdi+2224]
	mov rbp, QWORD PTR [rdi+2232]
	mov r12, QWORD PTR [rdi+2240]
	mov r13, QWORD PTR [rdi+2248]
	mov r14, QWORD PTR [rdi+2256]
	mov r15, QWORD PTR [rdi+2264]
	ret
	.p2align 6
