// The functions of `src/sha3.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha3_224_update:
	mov r9, r8
	mov r8, rcx
	mov rcx, rdx
	mov rdx, rsi
	mov esi, 144
	mov QWORD PTR [r9+512], rbx
	mov QWORD PTR [r9+520], rbp
	mov QWORD PTR [r9+528], r12
	mov QWORD PTR [r9+536], r13
	mov QWORD PTR [r9+544], r14
	mov QWORD PTR [r9+552], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	mov r10, r12
	mov r11d, 7
	and r10, r11
	mov r11, r14
	sub r11, 8
	shr r11, 63
	or r10, r11
	test r10, r10
	je 23f
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [rbx+r12*1]
	xor rax, rcx
	mov BYTE PTR [rbx+r12*1], al
	add r13, 1
	add r12, 1
	sub r14, 1
	cmp r12, rbp
	jmp 24f
23:
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [rbx+r12*1]
	mov QWORD PTR [rbx+r12*1], rax
	add r13, 8
	add r12, 8
	sub r14, 8
	cmp r12, rbp
24:
	je 25f
	jmp 26f
25:
	mov r12d, 0
	mov rdi, rbx
	mov rsi, r15
	call {vg_keccak_f1600}
	mov rbx, rdi
	mov r15, rsi
26:
	test r14, r14
	jne 22b
	jmp 21f
20:
21:
	mov rax, r12
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	ret
	.p2align 6

vg_sha3_224_finalize:
	lea rsp, [rsp-664]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+640], r12
	mov QWORD PTR [rcx+648], rbp
	mov r12, rcx
	mov rbp, rdx
	mov rdx, rsi
	mov esi, 144
	mov ecx, 6
	mov r8, r12
	call {vg_keccak_pad_scratch}
	mov esi, 144
	mov edx, 0
	mov rcx, rbp
	mov r8d, 28
	mov r9, r12
	call {vg_keccak_squeeze_scratch}
	mov rbp, QWORD PTR [r12+648]
	mov r12, QWORD PTR [r12+640]
	lea rsp, [rsp+664]
	ret
	.p2align 6

vg_sha3_256_update:
	mov r9, r8
	mov r8, rcx
	mov rcx, rdx
	mov rdx, rsi
	mov esi, 136
	mov QWORD PTR [r9+512], rbx
	mov QWORD PTR [r9+520], rbp
	mov QWORD PTR [r9+528], r12
	mov QWORD PTR [r9+536], r13
	mov QWORD PTR [r9+544], r14
	mov QWORD PTR [r9+552], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	mov r10, r12
	mov r11d, 7
	and r10, r11
	mov r11, r14
	sub r11, 8
	shr r11, 63
	or r10, r11
	test r10, r10
	je 23f
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [rbx+r12*1]
	xor rax, rcx
	mov BYTE PTR [rbx+r12*1], al
	add r13, 1
	add r12, 1
	sub r14, 1
	cmp r12, rbp
	jmp 24f
23:
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [rbx+r12*1]
	mov QWORD PTR [rbx+r12*1], rax
	add r13, 8
	add r12, 8
	sub r14, 8
	cmp r12, rbp
24:
	je 25f
	jmp 26f
25:
	mov r12d, 0
	mov rdi, rbx
	mov rsi, r15
	call {vg_keccak_f1600}
	mov rbx, rdi
	mov r15, rsi
26:
	test r14, r14
	jne 22b
	jmp 21f
20:
21:
	mov rax, r12
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	ret
	.p2align 6

vg_sha3_256_finalize:
	lea rsp, [rsp-664]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+640], r12
	mov QWORD PTR [rcx+648], rbp
	mov r12, rcx
	mov rbp, rdx
	mov rdx, rsi
	mov esi, 136
	mov ecx, 6
	mov r8, r12
	call {vg_keccak_pad_scratch}
	mov esi, 136
	mov edx, 0
	mov rcx, rbp
	mov r8d, 32
	mov r9, r12
	call {vg_keccak_squeeze_scratch}
	mov rbp, QWORD PTR [r12+648]
	mov r12, QWORD PTR [r12+640]
	lea rsp, [rsp+664]
	ret
	.p2align 6

vg_sha3_384_update:
	mov r9, r8
	mov r8, rcx
	mov rcx, rdx
	mov rdx, rsi
	mov esi, 104
	mov QWORD PTR [r9+512], rbx
	mov QWORD PTR [r9+520], rbp
	mov QWORD PTR [r9+528], r12
	mov QWORD PTR [r9+536], r13
	mov QWORD PTR [r9+544], r14
	mov QWORD PTR [r9+552], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	mov r10, r12
	mov r11d, 7
	and r10, r11
	mov r11, r14
	sub r11, 8
	shr r11, 63
	or r10, r11
	test r10, r10
	je 23f
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [rbx+r12*1]
	xor rax, rcx
	mov BYTE PTR [rbx+r12*1], al
	add r13, 1
	add r12, 1
	sub r14, 1
	cmp r12, rbp
	jmp 24f
23:
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [rbx+r12*1]
	mov QWORD PTR [rbx+r12*1], rax
	add r13, 8
	add r12, 8
	sub r14, 8
	cmp r12, rbp
24:
	je 25f
	jmp 26f
25:
	mov r12d, 0
	mov rdi, rbx
	mov rsi, r15
	call {vg_keccak_f1600}
	mov rbx, rdi
	mov r15, rsi
26:
	test r14, r14
	jne 22b
	jmp 21f
20:
21:
	mov rax, r12
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	ret
	.p2align 6

vg_sha3_384_finalize:
	lea rsp, [rsp-664]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+640], r12
	mov QWORD PTR [rcx+648], rbp
	mov r12, rcx
	mov rbp, rdx
	mov rdx, rsi
	mov esi, 104
	mov ecx, 6
	mov r8, r12
	call {vg_keccak_pad_scratch}
	mov esi, 104
	mov edx, 0
	mov rcx, rbp
	mov r8d, 48
	mov r9, r12
	call {vg_keccak_squeeze_scratch}
	mov rbp, QWORD PTR [r12+648]
	mov r12, QWORD PTR [r12+640]
	lea rsp, [rsp+664]
	ret
	.p2align 6

vg_sha3_512_update:
	mov r9, r8
	mov r8, rcx
	mov rcx, rdx
	mov rdx, rsi
	mov esi, 72
	mov QWORD PTR [r9+512], rbx
	mov QWORD PTR [r9+520], rbp
	mov QWORD PTR [r9+528], r12
	mov QWORD PTR [r9+536], r13
	mov QWORD PTR [r9+544], r14
	mov QWORD PTR [r9+552], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	mov r10, r12
	mov r11d, 7
	and r10, r11
	mov r11, r14
	sub r11, 8
	shr r11, 63
	or r10, r11
	test r10, r10
	je 23f
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [rbx+r12*1]
	xor rax, rcx
	mov BYTE PTR [rbx+r12*1], al
	add r13, 1
	add r12, 1
	sub r14, 1
	cmp r12, rbp
	jmp 24f
23:
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [rbx+r12*1]
	mov QWORD PTR [rbx+r12*1], rax
	add r13, 8
	add r12, 8
	sub r14, 8
	cmp r12, rbp
24:
	je 25f
	jmp 26f
25:
	mov r12d, 0
	mov rdi, rbx
	mov rsi, r15
	call {vg_keccak_f1600}
	mov rbx, rdi
	mov r15, rsi
26:
	test r14, r14
	jne 22b
	jmp 21f
20:
21:
	mov rax, r12
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	ret
	.p2align 6

vg_sha3_512_finalize:
	lea rsp, [rsp-664]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+640], r12
	mov QWORD PTR [rcx+648], rbp
	mov r12, rcx
	mov rbp, rdx
	mov rdx, rsi
	mov esi, 72
	mov ecx, 6
	mov r8, r12
	call {vg_keccak_pad_scratch}
	mov esi, 72
	mov edx, 0
	mov rcx, rbp
	mov r8d, 64
	mov r9, r12
	call {vg_keccak_squeeze_scratch}
	mov rbp, QWORD PTR [r12+648]
	mov r12, QWORD PTR [r12+640]
	lea rsp, [rsp+664]
	ret
	.p2align 6

vg_shake128_update:
	mov r9, r8
	mov r8, rcx
	mov rcx, rdx
	mov rdx, rsi
	mov esi, 168
	mov QWORD PTR [r9+512], rbx
	mov QWORD PTR [r9+520], rbp
	mov QWORD PTR [r9+528], r12
	mov QWORD PTR [r9+536], r13
	mov QWORD PTR [r9+544], r14
	mov QWORD PTR [r9+552], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	mov r10, r12
	mov r11d, 7
	and r10, r11
	mov r11, r14
	sub r11, 8
	shr r11, 63
	or r10, r11
	test r10, r10
	je 23f
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [rbx+r12*1]
	xor rax, rcx
	mov BYTE PTR [rbx+r12*1], al
	add r13, 1
	add r12, 1
	sub r14, 1
	cmp r12, rbp
	jmp 24f
23:
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [rbx+r12*1]
	mov QWORD PTR [rbx+r12*1], rax
	add r13, 8
	add r12, 8
	sub r14, 8
	cmp r12, rbp
24:
	je 25f
	jmp 26f
25:
	mov r12d, 0
	mov rdi, rbx
	mov rsi, r15
	call {vg_keccak_f1600}
	mov rbx, rdi
	mov r15, rsi
26:
	test r14, r14
	jne 22b
	jmp 21f
20:
21:
	mov rax, r12
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	ret
	.p2align 6

vg_shake128_finalize:
	lea rsp, [rsp-648]
	mov rdx, rsp
	add rdx, 8
	mov r8, rdx
	mov rdx, rsi
	mov esi, 168
	mov ecx, 31
	movzx eax, BYTE PTR [rdi+rdx*1]
	xor rax, rcx
	mov BYTE PTR [rdi+rdx*1], al
	movzx eax, BYTE PTR [rdi+rsi*1-1]
	xor rax, 128
	mov BYTE PTR [rdi+rsi*1-1], al
	mov rsi, r8
	call {vg_keccak_f1600}
	lea rsp, [rsp+648]
	ret
	.p2align 6

vg_shake128_squeeze:
	lea rsp, [rsp-648]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov r8, rcx
	mov rcx, rdx
	mov rdx, rsi
	mov esi, 168
	mov QWORD PTR [r9+512], rbx
	mov QWORD PTR [r9+520], rbp
	mov QWORD PTR [r9+528], r12
	mov QWORD PTR [r9+536], r13
	mov QWORD PTR [r9+544], r14
	mov QWORD PTR [r9+552], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	cmp r12, rbp
	je 23f
	jmp 24f
23:
	mov r12d, 0
	mov rdi, rbx
	mov rsi, r15
	call {vg_keccak_f1600}
	mov rbx, rdi
	mov r15, rsi
24:
	mov r10, r12
	mov r11d, 7
	and r10, r11
	mov r11, r14
	sub r11, 8
	shr r11, 63
	or r10, r11
	test r10, r10
	je 25f
	movzx eax, BYTE PTR [rbx+r12*1]
	mov BYTE PTR [r13], al
	add r13, 1
	add r12, 1
	sub r14, 1
	jmp 26f
25:
	mov rax, QWORD PTR [rbx+r12*1]
	mov QWORD PTR [r13], rax
	add r13, 8
	add r12, 8
	sub r14, 8
26:
	jne 22b
	jmp 21f
20:
21:
	mov rax, r12
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+648]
	ret
	.p2align 6

vg_shake256_finalize:
	lea rsp, [rsp-648]
	mov rdx, rsp
	add rdx, 8
	mov r8, rdx
	mov rdx, rsi
	mov esi, 136
	mov ecx, 31
	movzx eax, BYTE PTR [rdi+rdx*1]
	xor rax, rcx
	mov BYTE PTR [rdi+rdx*1], al
	movzx eax, BYTE PTR [rdi+rsi*1-1]
	xor rax, 128
	mov BYTE PTR [rdi+rsi*1-1], al
	mov rsi, r8
	call {vg_keccak_f1600}
	lea rsp, [rsp+648]
	ret
	.p2align 6

vg_shake256_squeeze:
	lea rsp, [rsp-648]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov r8, rcx
	mov rcx, rdx
	mov rdx, rsi
	mov esi, 136
	mov QWORD PTR [r9+512], rbx
	mov QWORD PTR [r9+520], rbp
	mov QWORD PTR [r9+528], r12
	mov QWORD PTR [r9+536], r13
	mov QWORD PTR [r9+544], r14
	mov QWORD PTR [r9+552], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	cmp r12, rbp
	je 23f
	jmp 24f
23:
	mov r12d, 0
	mov rdi, rbx
	mov rsi, r15
	call {vg_keccak_f1600}
	mov rbx, rdi
	mov r15, rsi
24:
	mov r10, r12
	mov r11d, 7
	and r10, r11
	mov r11, r14
	sub r11, 8
	shr r11, 63
	or r10, r11
	test r10, r10
	je 25f
	movzx eax, BYTE PTR [rbx+r12*1]
	mov BYTE PTR [r13], al
	add r13, 1
	add r12, 1
	sub r14, 1
	jmp 26f
25:
	mov rax, QWORD PTR [rbx+r12*1]
	mov QWORD PTR [r13], rax
	add r13, 8
	add r12, 8
	sub r14, 8
26:
	jne 22b
	jmp 21f
20:
21:
	mov rax, r12
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+648]
	ret
	.p2align 6
