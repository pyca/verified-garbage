// The functions of `src/internal/vg_slhdsa_shake_wots4_n16_avx512vl.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_wots4_n16_avx512vl:
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
	mov DWORD PTR [rbx+3332], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3844], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+3840], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3848], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3852], eax
	mov r10, r12
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3460], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+6052], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+6048], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+6056], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+6060], eax
	mov r10, r12
	add r10, 2
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3588], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+8260], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+8256], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+8264], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+8268], eax
	mov r10, r12
	add r10, 3
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3716], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+10468], eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+10464], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+10472], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+10476], eax
	mov r13d, 0
20:
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3328], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3336], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3340], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3344], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3352], rax
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3456], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3464], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3468], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3472], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3480], rax
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3584], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3592], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3596], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3600], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3608], rax
	mov eax, 5
	bswap eax
	mov DWORD PTR [rbx+3712], eax
	mov eax, r13d
	bswap eax
	mov DWORD PTR [rbx+3720], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3724], eax
	mov rax, QWORD PTR [rbx+3168]
	mov QWORD PTR [rbx+3728], rax
	mov rax, QWORD PTR [rbx+3176]
	mov QWORD PTR [rbx+3736], rax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 64
	mov rcx, rdi
	add rcx, 48
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n16_avx512vl}
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3328], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3456], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3584], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3712], eax
	mov ebp, 0
21:
	movzx ecx, BYTE PTR [rbx+r13*1+30368]
	mov rdx, rbp
	xor rdx, rcx
	mov rsi, r13
	shl rsi, 4
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
	mov rcx, QWORD PTR [rbx+3344]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3352]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, r12
	add rax, 1
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3472]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3480]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, r12
	add rax, 2
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3600]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3608]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, r12
	add rax, 3
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3728]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3736]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3340], eax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3468], eax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3596], eax
	mov eax, ebp
	bswap eax
	mov DWORD PTR [rbx+3724], eax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 64
	mov rcx, rdi
	add rcx, 48
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n16_avx512vl}
	add rbp, 1
	cmp rbp, 15
	jne 21b
	movzx ecx, BYTE PTR [rbx+r13*1+30368]
	mov rdx, rbp
	xor rdx, rcx
	mov rsi, r13
	shl rsi, 4
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
	mov rcx, QWORD PTR [rbx+3344]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3352]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, r12
	add rax, 1
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3472]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3480]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, r12
	add rax, 2
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3600]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3608]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rax, r12
	add rax, 3
	xor rax, r14
	or rax, rdx
	sub rax, 1
	shr rax, 63
	mov edi, 0
	sub rdi, rax
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rbx+3728]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rsi+8]
	mov rcx, QWORD PTR [rbx+3736]
	xor rcx, rax
	and rcx, rdi
	xor rax, rcx
	mov QWORD PTR [rsi+8], rax
	mov rdx, r13
	shl rdx, 4
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3344]
	mov QWORD PTR [rdx+3856], rax
	mov rax, QWORD PTR [rbx+3352]
	mov QWORD PTR [rdx+3864], rax
	mov rax, QWORD PTR [rbx+3472]
	mov QWORD PTR [rdx+6064], rax
	mov rax, QWORD PTR [rbx+3480]
	mov QWORD PTR [rdx+6072], rax
	mov rax, QWORD PTR [rbx+3600]
	mov QWORD PTR [rdx+8272], rax
	mov rax, QWORD PTR [rbx+3608]
	mov QWORD PTR [rdx+8280], rax
	mov rax, QWORD PTR [rbx+3728]
	mov QWORD PTR [rdx+10480], rax
	mov rax, QWORD PTR [rbx+3736]
	mov QWORD PTR [rdx+10488], rax
	add r13, 1
	cmp r13, 35
	jne 20b
	mov rdi, rbx
	add rdi, 3808
	mov esi, 2208
	mov edx, 608
	mov rcx, rdi
	add rcx, 48
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n16_avx512vl}
	mov rdx, r12
	shl rdx, 4
	add rdx, rbx
	add rdx, 12640
	mov rax, QWORD PTR [rbx+3856]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rbx+3864]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rbx+6064]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rbx+6072]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rbx+8272]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rbx+8280]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rbx+10480]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rbx+10488]
	mov QWORD PTR [rdx+56], rax
	mov r15, QWORD PTR [rbx+2440]
	mov r14, QWORD PTR [rbx+2432]
	mov r13, QWORD PTR [rbx+2424]
	mov r12, QWORD PTR [rbx+2416]
	mov rbp, QWORD PTR [rbx+2408]
	mov rbx, QWORD PTR [rbx+2400]
	ret
	.p2align 6
