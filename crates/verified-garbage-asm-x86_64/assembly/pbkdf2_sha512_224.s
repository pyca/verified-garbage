// The functions of `src/pbkdf2_sha512_224.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512_224_shani:
	lea rsp, [rsp-1800]
	mov rax, QWORD PTR [rsp+1808]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+240], rbx
	mov QWORD PTR [r8+248], rbp
	mov QWORD PTR [r8+256], r12
	mov QWORD PTR [r8+264], r13
	mov QWORD PTR [r8+272], r14
	mov QWORD PTR [r8+280], r15
	mov r15, r8
	mov QWORD PTR [r15+288], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+296], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 880
	call {vg_sha512_224_init_core}
	mov rdi, r15
	add rdi, 880
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rdi, r15
	add rdi, 880
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1128
	mov rcx, r15
	call {vg_sha512_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 1128
	mov ecx, 28
21:
	mov rdi, r15
	add rdi, 304
	mov rsi, r15
	add rsi, 496
	mov r8, r15
	call {vg_hmac_sha512_224_init_scratch_shani}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+304]
	mov BYTE PTR [r15+r14*1+688], al
	add r14, 1
	cmp r14, 192
	jne 22b
	mov rdi, r15
	add rdi, 688
	mov esi, 128
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rbp, r13
	mov r13, QWORD PTR [r15+288]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+688]
	mov BYTE PTR [r15+r14*1+880], al
	add r14, 1
	cmp r14, 192
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+1192], eax
	mov rdi, r15
	add rdi, 880
	mov rsi, rbp
	add rsi, 128
	mov rdx, r15
	add rdx, 1192
	mov ecx, 4
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rdi, r15
	add rdi, 880
	mov rsi, r15
	add rsi, 496
	mov rdx, rbp
	add rdx, 132
	mov rcx, r15
	add rcx, 1072
	mov r8, r15
	call {vg_hmac_sha512_224_finalize_scratch_shani}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+1072]
	mov BYTE PTR [r15+r14*1+1100], al
	add r14, 1
	cmp r14, 28
	jne 27b
	mov rdi, r15
	add rdi, 304
	mov rsi, r15
	add rsi, 1072
	mov rdx, QWORD PTR [r15+296]
	mov rcx, r15
	add rcx, 1100
	mov r8, r15
	call {vg_pbkdf2_hmac_sha512_224_iterate_shani}
	mov ecx, 28
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+1100]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+240]
	mov rbp, QWORD PTR [r15+248]
	mov r12, QWORD PTR [r15+256]
	mov r13, QWORD PTR [r15+264]
	mov r14, QWORD PTR [r15+272]
	mov r15, QWORD PTR [r15+280]
	lea rsp, [rsp+1800]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha512_224_avx2:
	lea rsp, [rsp-3128]
	mov rax, QWORD PTR [rsp+3136]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+1568], rbx
	mov QWORD PTR [r8+1576], rbp
	mov QWORD PTR [r8+1584], r12
	mov QWORD PTR [r8+1592], r13
	mov QWORD PTR [r8+1600], r14
	mov QWORD PTR [r8+1608], r15
	mov r15, r8
	mov QWORD PTR [r15+1616], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+1624], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 2208
	call {vg_sha512_224_init_core}
	mov rdi, r15
	add rdi, 2208
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rdi, r15
	add rdi, 2208
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2456
	mov rcx, r15
	call {vg_sha512_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 2456
	mov ecx, 28
21:
	mov rdi, r15
	add rdi, 1632
	mov rsi, r15
	add rsi, 1824
	mov r8, r15
	call {vg_hmac_sha512_224_init_scratch_avx2}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+1632]
	mov BYTE PTR [r15+r14*1+2016], al
	add r14, 1
	cmp r14, 192
	jne 22b
	mov rdi, r15
	add rdi, 2016
	mov esi, 128
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rbp, r13
	mov r13, QWORD PTR [r15+1616]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+2016]
	mov BYTE PTR [r15+r14*1+2208], al
	add r14, 1
	cmp r14, 192
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+2520], eax
	mov rdi, r15
	add rdi, 2208
	mov rsi, rbp
	add rsi, 128
	mov rdx, r15
	add rdx, 2520
	mov ecx, 4
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rdi, r15
	add rdi, 2208
	mov rsi, r15
	add rsi, 1824
	mov rdx, rbp
	add rdx, 132
	mov rcx, r15
	add rcx, 2400
	mov r8, r15
	call {vg_hmac_sha512_224_finalize_scratch_avx2}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+2400]
	mov BYTE PTR [r15+r14*1+2428], al
	add r14, 1
	cmp r14, 28
	jne 27b
	mov rdi, r15
	add rdi, 1632
	mov rsi, r15
	add rsi, 2400
	mov rdx, QWORD PTR [r15+1624]
	mov rcx, r15
	add rcx, 2428
	mov r8, r15
	call {vg_pbkdf2_hmac_sha512_224_iterate_avx2}
	mov ecx, 28
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+2428]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+1568]
	mov rbp, QWORD PTR [r15+1576]
	mov r12, QWORD PTR [r15+1584]
	mov r13, QWORD PTR [r15+1592]
	mov r14, QWORD PTR [r15+1600]
	mov r15, QWORD PTR [r15+1608]
	lea rsp, [rsp+3128]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha512_224:
	lea rsp, [rsp-1992]
	mov rax, QWORD PTR [rsp+2000]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+432], rbx
	mov QWORD PTR [r8+440], rbp
	mov QWORD PTR [r8+448], r12
	mov QWORD PTR [r8+456], r13
	mov QWORD PTR [r8+464], r14
	mov QWORD PTR [r8+472], r15
	mov r15, r8
	mov QWORD PTR [r15+480], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+488], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 129
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 1072
	call {vg_sha512_224_init_core}
	mov rdi, r15
	add rdi, 1072
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rdi, r15
	add rdi, 1072
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1320
	mov rcx, r15
	call {vg_sha512_finalize_scratch}
	mov rdx, r15
	add rdx, 1320
	mov ecx, 28
21:
	mov rdi, r15
	add rdi, 496
	mov rsi, r15
	add rsi, 688
	mov r8, r15
	call {vg_hmac_sha512_224_init_scratch}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+496]
	mov BYTE PTR [r15+r14*1+880], al
	add r14, 1
	cmp r14, 192
	jne 22b
	mov rdi, r15
	add rdi, 880
	mov esi, 128
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rbp, r13
	mov r13, QWORD PTR [r15+480]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+880]
	mov BYTE PTR [r15+r14*1+1072], al
	add r14, 1
	cmp r14, 192
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+1384], eax
	mov rdi, r15
	add rdi, 1072
	mov rsi, rbp
	add rsi, 128
	mov rdx, r15
	add rdx, 1384
	mov ecx, 4
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rdi, r15
	add rdi, 1072
	mov rsi, r15
	add rsi, 688
	mov rdx, rbp
	add rdx, 132
	mov rcx, r15
	add rcx, 1264
	mov r8, r15
	call {vg_hmac_sha512_224_finalize_scratch}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+1264]
	mov BYTE PTR [r15+r14*1+1292], al
	add r14, 1
	cmp r14, 28
	jne 27b
	mov rdi, r15
	add rdi, 496
	mov rsi, r15
	add rsi, 1264
	mov rdx, QWORD PTR [r15+488]
	mov rcx, r15
	add rcx, 1292
	mov r8, r15
	call {vg_pbkdf2_hmac_sha512_224_iterate}
	mov ecx, 28
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+1292]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+432]
	mov rbp, QWORD PTR [r15+440]
	mov r12, QWORD PTR [r15+448]
	mov r13, QWORD PTR [r15+456]
	mov r14, QWORD PTR [r15+464]
	mov r15, QWORD PTR [r15+472]
	lea rsp, [rsp+1992]
	ret
	.p2align 6
