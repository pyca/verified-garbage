// The functions of `src/internal/vg_slhdsa_shake_wots4_n24.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_wots4_n24:
	mov QWORD PTR [rdi+2400], rbx
	mov QWORD PTR [rdi+2408], rbp
	mov QWORD PTR [rdi+2416], r12
	mov QWORD PTR [rdi+2424], r13
	mov QWORD PTR [rdi+2432], r14
	mov QWORD PTR [rdi+2440], r15
	mov rbx, rdi
	mov r12, rsi
	mov r14, rdx
	mov r15, rcx
	mov r10, r12
	add r10, 0
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3340], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3852], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+3848], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3856], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3860], eax
	mov r10, r12
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3468], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+6060], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+6056], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+6064], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+6068], eax
	mov r10, r12
	add r10, 2
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3596], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+8268], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+8264], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+8272], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+8276], eax
	mov r10, r12
	add r10, 3
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3724], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+10476], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+10472], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+10480], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+10484], eax
	mov r13d, 0
20:
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3336], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3348], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3352], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rbx+3184]
	mov QWORD PTR [rbx+3368], rax
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3464], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3472], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3476], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3480], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rbx+3184]
	mov QWORD PTR [rbx+3496], rax
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3592], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3600], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3604], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3608], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rbx+3184]
	mov QWORD PTR [rbx+3624], rax
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3720], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3728], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3732], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3736], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rbx+3184]
	mov QWORD PTR [rbx+3752], rax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 80
	mov rcx, rdi
	add rcx, 56
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n24}
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3336], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3464], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3592], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3720], eax
	mov ebp, 0
21:
	movzx ecx, BYTE PTR [rbx+r13*1+30368]
	mov rdx, rbp
	xor rdx, rcx
	mov rsi, r13
	mov rax, rsi
	shl rsi, 4
	shl rax, 3
	add rsi, rax
	add rsi, r15
	mov rax, r12
	add rax, 0
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3352]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3360]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3368]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, r12
	add rax, 1
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3480]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3488]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3496]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, r12
	add rax, 2
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3608]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3616]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3624]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, r12
	add rax, 3
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3736]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3744]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3752]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3348], eax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3476], eax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3604], eax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3732], eax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 80
	mov rcx, rdi
	add rcx, 56
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n24}
	add rbp, 1
	cmp rbp, 15
	jne 21b
	movzx ecx, BYTE PTR [rbx+r13*1+30368]
	mov rdx, rbp
	xor rdx, rcx
	mov rsi, r13
	mov rax, rsi
	shl rsi, 4
	shl rax, 3
	add rsi, rax
	add rsi, r15
	mov rax, r12
	add rax, 0
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3352]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3360]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3368]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, r12
	add rax, 1
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3480]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3488]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3496]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, r12
	add rax, 2
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3608]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3616]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3624]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rax, r12
	add rax, 3
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3736]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3744]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov rcx, QWORD PTR [rbx+3752]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+16], rax
	mov rdx, r13
	mov rax, rdx
	shl rdx, 4
	shl rax, 3
	add rdx, rax
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3352]
	mov QWORD PTR [rdx+3864], rax
	mov rax, QWORD PTR [rbx+3360]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+3368]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+3480]
	mov QWORD PTR [rdx+6072], rax
	mov rax, QWORD PTR [rbx+3488]
	mov QWORD PTR [rdx+6080], rax
	mov rax, QWORD PTR [rbx+3496]
	mov QWORD PTR [rdx+6088], rax
	mov rax, QWORD PTR [rbx+3608]
	mov QWORD PTR [rdx+8280], rax
	mov rax, QWORD PTR [rbx+3616]
	mov QWORD PTR [rdx+8288], rax
	mov rax, QWORD PTR [rbx+3624]
	mov QWORD PTR [rdx+8296], rax
	mov rax, QWORD PTR [rbx+3736]
	mov QWORD PTR [rdx+10488], rax
	mov rax, QWORD PTR [rbx+3744]
	mov QWORD PTR [rdx+10496], rax
	mov rax, QWORD PTR [rbx+3752]
	mov QWORD PTR [rdx+10504], rax
	add r13, 1
	cmp r13, 51
	jne 20b
	mov rdi, rbx
	add rdi, 3808
	mov esi, 2208
	mov edx, 1280
	mov rcx, rdi
	add rcx, 56
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n24}
	mov rdx, r12
	mov rax, rdx
	shl rdx, 4
	shl rax, 3
	add rdx, rax
	add rdx, rbx
	add rdx, 12640
	mov rax, QWORD PTR [rbx+3864]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rbx+3872]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rbx+3880]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rbx+6072]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rbx+6080]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rbx+6088]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rbx+8280]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rbx+8288]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rbx+8296]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rbx+10488]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rbx+10496]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rbx+10504]
	mov QWORD PTR [rdx+88], rax
	mov r15, QWORD PTR [rbx+2440]
	mov r14, QWORD PTR [rbx+2432]
	mov r13, QWORD PTR [rbx+2424]
	mov r12, QWORD PTR [rbx+2416]
	mov rbp, QWORD PTR [rbx+2408]
	mov rbx, QWORD PTR [rbx+2400]
	ret
	.p2align 6
