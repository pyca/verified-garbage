// The functions of `src/internal/vg_dsa_parameter_search_1024_sha1_shani_mr_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_parameter_search_1024_sha1_shani_mr_adx:
	lea rsp, [rsp-48]
	mov QWORD PTR [rsp], rbx
	mov QWORD PTR [rsp+8], rbp
	mov QWORD PTR [rsp+16], r12
	mov QWORD PTR [rsp+24], r13
	mov QWORD PTR [rsp+32], r14
	mov QWORD PTR [rsp+40], r15
	lea rsp, [rsp-32]
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+48], rdi
	mov QWORD PTR [rsp+56], rsi
	mov QWORD PTR [rsp+296], rdx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], r8
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+120], r8
	mov QWORD PTR [rsp+88], rcx
	mov eax, 0
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+40], r9
	mov eax, 128
	mov QWORD PTR [rsp+136], rax
	mov eax, 20
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rax]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 24576
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 24640
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 16384
	mov QWORD PTR [rsp+112], rax
	mov eax, 0
	mov QWORD PTR [rsp+128], rax
20:
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+320], rax
	mov rcx, QWORD PTR [rsp+312]
	test rcx, rcx
	je 21f
	mov rcx, QWORD PTR [rsp+120]
	sub rcx, rax
	cmp rcx, 20
	jb 23f
	mov rcx, QWORD PTR [rsp+104]
	add rcx, rax
	mov QWORD PTR [rsp+8], rcx
	add rax, 20
	mov QWORD PTR [rsp+128], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25408
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rsp+216], rax
	mov eax, 20
	mov QWORD PTR [rsp+224], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp]
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+224]
	mov rdx, rcx
	shl rdx, 3
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
25:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 25b
	movzx eax, BYTE PTR [r11-1]
	or rax, 1
	mov BYTE PTR [r11-1], al
	mov rdi, QWORD PTR [rsp+40]
	mov esi, 5120
	mov rdx, QWORD PTR [rsp+104]
	add rdx, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+120]
	sub rcx, QWORD PTR [rsp+128]
	mov r8, rsp
	add r8, 152
	mov r9d, 160
	call {vg_dsa_probable_prime_adx}
	mov eax, eax
	test rax, rax
	je 26f
	mov rcx, QWORD PTR [rsp+152]
	add rcx, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+128], rcx
	jmp 27f
26:
27:
	mov rcx, rax
	shr rcx, 1
	add rax, rcx
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 28f
	jmp 29f
28:
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 27840
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov eax, 1
	mov QWORD PTR [rdi+8], rax
210:
	mov rcx, QWORD PTR [rdi+8]
	mov rax, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+24]
	add rax, 25024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+216], rdx
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 0
	movzx ecx, BYTE PTR [rsi+19]
	add rax, rcx
	mov BYTE PTR [rdi+19], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+18]
	add rax, rcx
	mov BYTE PTR [rdi+18], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+17]
	add rax, rcx
	mov BYTE PTR [rdi+17], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+16]
	add rax, rcx
	mov BYTE PTR [rdi+16], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+15]
	add rax, rcx
	mov BYTE PTR [rdi+15], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+14]
	add rax, rcx
	mov BYTE PTR [rdi+14], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+13]
	add rax, rcx
	mov BYTE PTR [rdi+13], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+12]
	add rax, rcx
	mov BYTE PTR [rdi+12], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+11]
	add rax, rcx
	mov BYTE PTR [rdi+11], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+10]
	add rax, rcx
	mov BYTE PTR [rdi+10], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+9]
	add rax, rcx
	mov BYTE PTR [rdi+9], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+8]
	add rax, rcx
	mov BYTE PTR [rdi+8], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+7]
	add rax, rcx
	mov BYTE PTR [rdi+7], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+6]
	add rax, rcx
	mov BYTE PTR [rdi+6], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+5]
	add rax, rcx
	mov BYTE PTR [rdi+5], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+4]
	add rax, rcx
	mov BYTE PTR [rdi+4], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+3]
	add rax, rcx
	mov BYTE PTR [rdi+3], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+2]
	add rax, rcx
	mov BYTE PTR [rdi+2], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+1]
	add rax, rcx
	mov BYTE PTR [rdi+1], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi]
	add rax, rcx
	mov BYTE PTR [rdi], al
	shr rax, 8
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 120
	mov ecx, 20
	mov edx, 160
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
211:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 211b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 1
	movzx ecx, BYTE PTR [rsi+19]
	add rax, rcx
	mov BYTE PTR [rdi+19], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+18]
	add rax, rcx
	mov BYTE PTR [rdi+18], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+17]
	add rax, rcx
	mov BYTE PTR [rdi+17], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+16]
	add rax, rcx
	mov BYTE PTR [rdi+16], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+15]
	add rax, rcx
	mov BYTE PTR [rdi+15], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+14]
	add rax, rcx
	mov BYTE PTR [rdi+14], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+13]
	add rax, rcx
	mov BYTE PTR [rdi+13], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+12]
	add rax, rcx
	mov BYTE PTR [rdi+12], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+11]
	add rax, rcx
	mov BYTE PTR [rdi+11], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+10]
	add rax, rcx
	mov BYTE PTR [rdi+10], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+9]
	add rax, rcx
	mov BYTE PTR [rdi+9], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+8]
	add rax, rcx
	mov BYTE PTR [rdi+8], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+7]
	add rax, rcx
	mov BYTE PTR [rdi+7], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+6]
	add rax, rcx
	mov BYTE PTR [rdi+6], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+5]
	add rax, rcx
	mov BYTE PTR [rdi+5], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+4]
	add rax, rcx
	mov BYTE PTR [rdi+4], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+3]
	add rax, rcx
	mov BYTE PTR [rdi+3], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+2]
	add rax, rcx
	mov BYTE PTR [rdi+2], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+1]
	add rax, rcx
	mov BYTE PTR [rdi+1], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi]
	add rax, rcx
	mov BYTE PTR [rdi], al
	shr rax, 8
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 100
	mov ecx, 20
	mov edx, 160
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
212:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 212b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 2
	movzx ecx, BYTE PTR [rsi+19]
	add rax, rcx
	mov BYTE PTR [rdi+19], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+18]
	add rax, rcx
	mov BYTE PTR [rdi+18], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+17]
	add rax, rcx
	mov BYTE PTR [rdi+17], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+16]
	add rax, rcx
	mov BYTE PTR [rdi+16], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+15]
	add rax, rcx
	mov BYTE PTR [rdi+15], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+14]
	add rax, rcx
	mov BYTE PTR [rdi+14], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+13]
	add rax, rcx
	mov BYTE PTR [rdi+13], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+12]
	add rax, rcx
	mov BYTE PTR [rdi+12], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+11]
	add rax, rcx
	mov BYTE PTR [rdi+11], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+10]
	add rax, rcx
	mov BYTE PTR [rdi+10], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+9]
	add rax, rcx
	mov BYTE PTR [rdi+9], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+8]
	add rax, rcx
	mov BYTE PTR [rdi+8], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+7]
	add rax, rcx
	mov BYTE PTR [rdi+7], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+6]
	add rax, rcx
	mov BYTE PTR [rdi+6], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+5]
	add rax, rcx
	mov BYTE PTR [rdi+5], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+4]
	add rax, rcx
	mov BYTE PTR [rdi+4], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+3]
	add rax, rcx
	mov BYTE PTR [rdi+3], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+2]
	add rax, rcx
	mov BYTE PTR [rdi+2], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+1]
	add rax, rcx
	mov BYTE PTR [rdi+1], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi]
	add rax, rcx
	mov BYTE PTR [rdi], al
	shr rax, 8
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 80
	mov ecx, 20
	mov edx, 160
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
213:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 213b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 3
	movzx ecx, BYTE PTR [rsi+19]
	add rax, rcx
	mov BYTE PTR [rdi+19], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+18]
	add rax, rcx
	mov BYTE PTR [rdi+18], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+17]
	add rax, rcx
	mov BYTE PTR [rdi+17], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+16]
	add rax, rcx
	mov BYTE PTR [rdi+16], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+15]
	add rax, rcx
	mov BYTE PTR [rdi+15], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+14]
	add rax, rcx
	mov BYTE PTR [rdi+14], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+13]
	add rax, rcx
	mov BYTE PTR [rdi+13], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+12]
	add rax, rcx
	mov BYTE PTR [rdi+12], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+11]
	add rax, rcx
	mov BYTE PTR [rdi+11], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+10]
	add rax, rcx
	mov BYTE PTR [rdi+10], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+9]
	add rax, rcx
	mov BYTE PTR [rdi+9], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+8]
	add rax, rcx
	mov BYTE PTR [rdi+8], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+7]
	add rax, rcx
	mov BYTE PTR [rdi+7], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+6]
	add rax, rcx
	mov BYTE PTR [rdi+6], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+5]
	add rax, rcx
	mov BYTE PTR [rdi+5], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+4]
	add rax, rcx
	mov BYTE PTR [rdi+4], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+3]
	add rax, rcx
	mov BYTE PTR [rdi+3], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+2]
	add rax, rcx
	mov BYTE PTR [rdi+2], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+1]
	add rax, rcx
	mov BYTE PTR [rdi+1], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi]
	add rax, rcx
	mov BYTE PTR [rdi], al
	shr rax, 8
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 60
	mov ecx, 20
	mov edx, 160
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
214:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 214b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 4
	movzx ecx, BYTE PTR [rsi+19]
	add rax, rcx
	mov BYTE PTR [rdi+19], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+18]
	add rax, rcx
	mov BYTE PTR [rdi+18], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+17]
	add rax, rcx
	mov BYTE PTR [rdi+17], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+16]
	add rax, rcx
	mov BYTE PTR [rdi+16], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+15]
	add rax, rcx
	mov BYTE PTR [rdi+15], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+14]
	add rax, rcx
	mov BYTE PTR [rdi+14], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+13]
	add rax, rcx
	mov BYTE PTR [rdi+13], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+12]
	add rax, rcx
	mov BYTE PTR [rdi+12], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+11]
	add rax, rcx
	mov BYTE PTR [rdi+11], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+10]
	add rax, rcx
	mov BYTE PTR [rdi+10], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+9]
	add rax, rcx
	mov BYTE PTR [rdi+9], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+8]
	add rax, rcx
	mov BYTE PTR [rdi+8], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+7]
	add rax, rcx
	mov BYTE PTR [rdi+7], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+6]
	add rax, rcx
	mov BYTE PTR [rdi+6], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+5]
	add rax, rcx
	mov BYTE PTR [rdi+5], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+4]
	add rax, rcx
	mov BYTE PTR [rdi+4], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+3]
	add rax, rcx
	mov BYTE PTR [rdi+3], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+2]
	add rax, rcx
	mov BYTE PTR [rdi+2], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+1]
	add rax, rcx
	mov BYTE PTR [rdi+1], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi]
	add rax, rcx
	mov BYTE PTR [rdi], al
	shr rax, 8
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 40
	mov ecx, 20
	mov edx, 160
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
215:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 215b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 5
	movzx ecx, BYTE PTR [rsi+19]
	add rax, rcx
	mov BYTE PTR [rdi+19], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+18]
	add rax, rcx
	mov BYTE PTR [rdi+18], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+17]
	add rax, rcx
	mov BYTE PTR [rdi+17], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+16]
	add rax, rcx
	mov BYTE PTR [rdi+16], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+15]
	add rax, rcx
	mov BYTE PTR [rdi+15], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+14]
	add rax, rcx
	mov BYTE PTR [rdi+14], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+13]
	add rax, rcx
	mov BYTE PTR [rdi+13], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+12]
	add rax, rcx
	mov BYTE PTR [rdi+12], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+11]
	add rax, rcx
	mov BYTE PTR [rdi+11], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+10]
	add rax, rcx
	mov BYTE PTR [rdi+10], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+9]
	add rax, rcx
	mov BYTE PTR [rdi+9], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+8]
	add rax, rcx
	mov BYTE PTR [rdi+8], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+7]
	add rax, rcx
	mov BYTE PTR [rdi+7], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+6]
	add rax, rcx
	mov BYTE PTR [rdi+6], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+5]
	add rax, rcx
	mov BYTE PTR [rdi+5], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+4]
	add rax, rcx
	mov BYTE PTR [rdi+4], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+3]
	add rax, rcx
	mov BYTE PTR [rdi+3], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+2]
	add rax, rcx
	mov BYTE PTR [rdi+2], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+1]
	add rax, rcx
	mov BYTE PTR [rdi+1], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi]
	add rax, rcx
	mov BYTE PTR [rdi], al
	shr rax, 8
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 20
	mov ecx, 20
	mov edx, 160
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
216:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 216b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 6
	movzx ecx, BYTE PTR [rsi+19]
	add rax, rcx
	mov BYTE PTR [rdi+19], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+18]
	add rax, rcx
	mov BYTE PTR [rdi+18], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+17]
	add rax, rcx
	mov BYTE PTR [rdi+17], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+16]
	add rax, rcx
	mov BYTE PTR [rdi+16], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+15]
	add rax, rcx
	mov BYTE PTR [rdi+15], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+14]
	add rax, rcx
	mov BYTE PTR [rdi+14], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+13]
	add rax, rcx
	mov BYTE PTR [rdi+13], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+12]
	add rax, rcx
	mov BYTE PTR [rdi+12], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+11]
	add rax, rcx
	mov BYTE PTR [rdi+11], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+10]
	add rax, rcx
	mov BYTE PTR [rdi+10], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+9]
	add rax, rcx
	mov BYTE PTR [rdi+9], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+8]
	add rax, rcx
	mov BYTE PTR [rdi+8], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+7]
	add rax, rcx
	mov BYTE PTR [rdi+7], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+6]
	add rax, rcx
	mov BYTE PTR [rdi+6], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+5]
	add rax, rcx
	mov BYTE PTR [rdi+5], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+4]
	add rax, rcx
	mov BYTE PTR [rdi+4], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+3]
	add rax, rcx
	mov BYTE PTR [rdi+3], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+2]
	add rax, rcx
	mov BYTE PTR [rdi+2], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi+1]
	add rax, rcx
	mov BYTE PTR [rdi+1], al
	shr rax, 8
	movzx ecx, BYTE PTR [rsi]
	add rax, rcx
	mov BYTE PTR [rdi], al
	shr rax, 8
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 0
	mov ecx, 20
	mov edx, 160
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
217:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 217b
	mov rsi, QWORD PTR [rsp+32]
	add rsi, 12
	mov rdi, QWORD PTR [rsp]
	mov ecx, 128
	mov edx, 1024
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
218:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 218b
	movzx eax, BYTE PTR [r11-1]
	or rax, 1
	mov BYTE PTR [r11-1], al
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 28672
	mov r12d, 16
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov eax, 144
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25024
	mov QWORD PTR [rdi+128], rax
	mov rax, 128
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25408
	mov QWORD PTR [rdi+144], rax
	mov rax, 20
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25472
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25856
	mov QWORD PTR [rdi+168], rax
	mov rax, -1
	mov QWORD PTR [rdi+176], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
219:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 219b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+136]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
220:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 221f
	jmp 222f
221:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
222:
	test rdx, rdx
	jne 220b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
223:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 223b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+144]
	mov rcx, QWORD PTR [rdi+152]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
224:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 225f
	jmp 226f
225:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
226:
	test rdx, rdx
	jne 224b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
227:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 227b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
228:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 228b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov r11, r12
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13d, 0
	mov eax, 0
	mov r14, 0
229:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 229b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
230:
	mov ebp, 0
	mov rbx, rdi
	add rbx, 256
	mov r14, 0
231:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 231b
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
232:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 232b
	sub r12, 1
	mov ebp, 0
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, r10
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
233:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 233b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
234:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 234b
	sub r12, 1
	mov rax, rbp
	add rax, 1
	mov rbx, rdi
	add rbx, 256
	mov rdx, QWORD PTR [rbx]
	add rdx, rax
	mov QWORD PTR [rbx], rdx
	add r13, 1
	cmp r13, r11
	jne 230b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov r8, r9
	add r8, r8
	add r8, r8
	add r8, rdi
	add r8, 256
	mov r10, r9
	add r10, rdi
	add r10, 256
	mov rsi, r9
	add rsi, rsi
	add rsi, rsi
	add rsi, r9
	add rsi, rdi
	add rsi, 256
	mov r14, 0
235:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 235b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	add rax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov rbx, rdi
	add rbx, 256
	mov r14, 0
236:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 236b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+160]
	mov rcx, QWORD PTR [rdi+136]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
237:
	mov rbp, rdx
	and rbp, 7
	je 238f
	jmp 239f
238:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
239:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 237b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+136]
	mov r15, QWORD PTR [rdi+176]
	mov edx, 0
	mov r14, rsi
	add r14, rcx
240:
	mov rbp, rdx
	and rbp, 7
	je 241f
	jmp 242f
241:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
242:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 240b
	mov rsi, QWORD PTR [rdi+160]
	movzx eax, BYTE PTR [rsi]
	cmp rax, 128
	jb 243f
	mov rdi, QWORD PTR [rsp+40]
	mov esi, 5120
	mov rdx, QWORD PTR [rsp+104]
	add rdx, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+120]
	sub rcx, QWORD PTR [rsp+128]
	mov r8, rsp
	add r8, 152
	mov r9d, 1024
	call {vg_dsa_probable_prime_adx}
	mov eax, eax
	test rax, rax
	je 245f
	mov rcx, QWORD PTR [rsp+152]
	add rcx, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+128], rcx
	jmp 246f
245:
246:
	mov rcx, rax
	shr rcx, 1
	add rax, rcx
	mov QWORD PTR [rsp+152], rax
	jmp 244f
243:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
244:
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 27840
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+16]
	cmp rax, 3
	je 247f
	jmp 248f
247:
	mov rax, QWORD PTR [rdi]
	add rax, 1
	mov QWORD PTR [rdi], rax
	mov rcx, QWORD PTR [rdi+8]
	add rcx, 7
	mov QWORD PTR [rdi+8], rcx
	cmp rax, 4096
	jb 249f
	mov eax, 2
	mov QWORD PTR [rdi+16], rax
	jmp 250f
249:
	mov eax, 3
	mov QWORD PTR [rdi+16], rax
250:
248:
	mov rax, QWORD PTR [rdi+16]
	cmp rax, 3
	je 210b
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 251f
	jmp 252f
251:
	mov rax, QWORD PTR [rsp+104]
	add rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+88], rax
	mov rcx, QWORD PTR [rsp+120]
	sub rcx, QWORD PTR [rsp+128]
	cmp rcx, 16384
	jb 253f
	mov eax, 16384
	mov QWORD PTR [rsp+96], rax
	jmp 254f
253:
	mov QWORD PTR [rsp+96], rcx
254:
	mov eax, 0
	mov QWORD PTR [rsp+160], rax
255:
	mov rcx, QWORD PTR [rsp+96]
	mov rax, QWORD PTR [rsp+160]
	sub rcx, rax
	cmp rcx, 128
	jb 256f
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+160]
	add rax, rcx
	add rcx, 128
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+160], rcx
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 28672
	mov r12d, 16
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov eax, 144
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25472
	mov QWORD PTR [rdi+128], rax
	mov rax, 128
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 0
	mov QWORD PTR [rdi+144], rax
	mov rax, 128
	mov QWORD PTR [rdi+152], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
258:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+136]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
259:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 260f
	jmp 261f
260:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
261:
	test rdx, rdx
	jne 259b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
262:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 262b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+144]
	mov rcx, QWORD PTR [rdi+152]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
263:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 264f
	jmp 265f
264:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
265:
	test rdx, rdx
	jne 263b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rax, QWORD PTR [rbx]
	sub rax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
266:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 266b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
267:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 267b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	test rax, rax
	je 268f
	mov rdi, QWORD PTR [rsp+40]
	mov rax, QWORD PTR [rsp+168]
	mov QWORD PTR [rdi+272], rax
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, rdi
	add rax, 25472
	mov QWORD PTR [rdi+256], rax
	mov rax, rdi
	add rax, 25856
	mov QWORD PTR [rdi+288], rax
	mov eax, 128
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
270:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 270b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
271:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 272f
	jmp 273f
272:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
273:
	test rdx, rdx
	jne 271b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 26240
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
274:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 274b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 275f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 277f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 279f
281:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 281b
	jmp 280f
279:
280:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
282:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 282b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
283:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
284:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 284b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
285:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 285b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
286:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 286b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 283b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
287:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 288f
	mov eax, 0
	mov r14, 0
290:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 290b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
291:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
292:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 292b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
293:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 293b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 291b
	mov ebp, 0
	mov r14, 0
294:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 294b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
295:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 295b
	jmp 289f
288:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
296:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 296b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
297:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
298:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 298b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 297b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
299:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 299b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2100:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2101:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2101b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2100b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2102:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2102b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2103:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2103b
289:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 287b
	jmp 278f
277:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2104:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2105:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2105b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2106:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2107:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2108:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2108b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2109:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2109b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2110:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2110b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2106b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2111:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2112f
	mov eax, 0
	mov r14, 0
2114:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2114b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2115:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2116:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2116b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2117:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2117b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2115b
	mov ebp, 0
	mov r14, 0
2118:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2118b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2119:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	jmp 2113f
2112:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2120:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2120b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2121:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2122:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2122b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2121b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2123:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2123b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2124:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2125:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2125b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2124b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2126:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2127:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2127b
2113:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2111b
278:
	jmp 276f
275:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2128:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2128b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2129:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2130:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2130b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2131:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2131b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2132:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2132b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2129b
276:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2133:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2133b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2134:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2135f
	jmp 2136f
2135:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2136:
	test rdx, rdx
	jne 2134b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2137f
	mov eax, 0
	mov r14, 0
2139:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2139b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2140:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2141:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2141b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2142:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2142b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2140b
	mov ebp, 0
	mov r14, 0
2143:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2143b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2144:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2144b
	jmp 2138f
2137:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2145:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2145b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2146:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2147:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2147b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2146b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2148:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2148b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2149:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2150:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2150b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2149b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2151:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2151b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2152:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2152b
2138:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2153f
	mov eax, 0
	mov r14, 0
2155:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2155b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2156:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2157:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2157b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2158:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2158b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2156b
	mov ebp, 0
	mov r14, 0
2159:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2159b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2160:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2160b
	jmp 2154f
2153:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2161:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2161b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2162:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2163:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2163b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2162b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2164:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2164b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2165:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2166:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2166b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2165b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2167:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2167b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2168:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2168b
2154:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
2169:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2170:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2170b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2171:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2171b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2172:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2172b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2173:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2174f
	mov eax, 0
	mov r14, 0
2176:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2176b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2177:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2178:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2178b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2179:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2179b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2177b
	mov ebp, 0
	mov r14, 0
2180:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2180b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2181:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	jmp 2175f
2174:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2182:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2182b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2183:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2184:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2184b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2183b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2185:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2185b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2186:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2187:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2187b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2186b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2188:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2188b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2189:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2189b
2175:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
2190:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2190b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2173b
2191:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2192:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2193:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2194f
	mov eax, 0
	mov r14, 0
2196:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2196b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2197:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2198:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2198b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2199:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2199b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2197b
	mov ebp, 0
	mov r14, 0
2200:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2200b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2201:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2201b
	jmp 2195f
2194:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2202:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2202b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2203:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2204:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2204b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2203b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2205:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2205b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2206:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2207:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2207b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2206b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2208:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2208b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2209:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2209b
2195:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2193b
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+216]
	test rax, rax
	je 2210f
	mov r12, QWORD PTR [rdi+48]
	mov rax, r12
	add rax, 2
	mov rdx, QWORD PTR [rdi+216]
	imul rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	mov rsi, QWORD PTR [rdi+200]
	add rsi, rax
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2212:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2212b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2213f
	mov eax, 0
	mov r14, 0
2215:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2215b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2216:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2217:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2217b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2218:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2218b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2216b
	mov ebp, 0
	mov r14, 0
2219:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2219b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2220:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2220b
	jmp 2214f
2213:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2221:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2221b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2222:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2223:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2223b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2222b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2224:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2224b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2225:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2226:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2226b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2225b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2227:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2227b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2228:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2228b
2214:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	jmp 2211f
2210:
2211:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2192b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2191b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 2229f
	mov eax, 0
	mov r14, 0
2231:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2231b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2232:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2233:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2233b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
2234:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 2234b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 2232b
	mov ebp, 0
	mov r14, 0
2235:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2235b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2236:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2236b
	jmp 2230f
2229:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
2237:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2237b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2238:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2239:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2239b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2238b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2240:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 2240b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2241:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2242:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 2242b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 2241b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2243:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2243b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2244:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2244b
2230:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2245:
	mov rbp, rdx
	and rbp, 7
	je 2246f
	jmp 2247f
2246:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2247:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2245b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 28672
	mov r12d, 16
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov eax, 144
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25472
	mov QWORD PTR [rdi+128], rax
	mov rax, 128
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 26240
	mov QWORD PTR [rdi+144], rax
	mov rax, 128
	mov QWORD PTR [rdi+152], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2248:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2248b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+136]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2249:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2250f
	jmp 2251f
2250:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2251:
	test rdx, rdx
	jne 2249b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2252:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2252b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	mov rsi, QWORD PTR [rdi+144]
	mov rcx, QWORD PTR [rdi+152]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2253:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2254f
	jmp 2255f
2254:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2255:
	test rdx, rdx
	jne 2253b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
2256:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2256b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
2257:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2257b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	test rax, rax
	je 2258f
	mov eax, 1
	mov QWORD PTR [rsp+152], rax
	jmp 2259f
2258:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
2259:
	jmp 269f
268:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
269:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 3
	jmp 257f
256:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
	mov eax, 1
	test rax, rax
257:
	je 255b
	mov rax, QWORD PTR [rsp+128]
	add rax, QWORD PTR [rsp+160]
	mov QWORD PTR [rsp+128], rax
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2260f
	mov rax, QWORD PTR [rsp+96]
	cmp rax, 16384
	jb 2262f
	jmp 2263f
2262:
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
2263:
	jmp 2261f
2260:
2261:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2264f
	jmp 2265f
2264:
	mov rsi, QWORD PTR [rsp+40]
	mov rdi, rsi
	add rsi, 25472
	add rdi, 27008
	mov ecx, 128
	mov edx, 1024
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
2266:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2266b
	mov rsi, QWORD PTR [rsp+40]
	mov rdi, rsi
	add rsi, 25408
	add rdi, 27136
	mov ecx, 20
	mov edx, 160
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
2267:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2267b
	mov rsi, QWORD PTR [rsp+40]
	mov rdi, rsi
	add rsi, 26240
	add rdi, 27156
	mov ecx, 128
	mov edx, 1024
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
2268:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2268b
	mov rdi, QWORD PTR [rsp+40]
	mov r8, rdi
	add rdi, 27008
	add r8, 40960
	mov edx, 128
	mov ecx, 20
	mov esi, 276
	mov r9d, 2048
	call {vg_dsa_generation_check_parameters}
	test rax, rax
	je 2269f
	mov eax, 1
	mov QWORD PTR [rsp+152], rax
	jmp 2270f
2269:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
2270:
2265:
252:
29:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 3
	je 2271f
	jmp 2272f
2271:
	mov rax, QWORD PTR [rsp+312]
	sub rax, 1
	mov QWORD PTR [rsp+312], rax
2272:
	jmp 24f
23:
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
24:
	jmp 22f
21:
	mov eax, 2
	mov QWORD PTR [rsp+152], rax
22:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 3
	je 20b
	mov rax, QWORD PTR [rsp+152]
	test rax, rax
	je 2273f
	mov rcx, QWORD PTR [rsp+304]
	mov eax, 0
	mov QWORD PTR [rcx], rax
	mov QWORD PTR [rcx+24], rax
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2275f
	mov rax, QWORD PTR [rsp+320]
	mov rcx, QWORD PTR [rsp+296]
	mov QWORD PTR [rcx], rax
	jmp 2276f
2275:
	mov rax, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+296]
	mov QWORD PTR [rcx], rax
2276:
	jmp 2274f
2273:
	mov rcx, QWORD PTR [rsp+120]
	sub rcx, QWORD PTR [rsp+320]
	mov edx, 4194432
	cmp rcx, rdx
	jb 2277f
	mov eax, 2
	mov QWORD PTR [rsp+152], rax
	jmp 2278f
2277:
	mov eax, 32768
	cmp rcx, rax
	jb 2279f
	mov rax, rcx
	jmp 2280f
2279:
2280:
	add rax, rax
	cmp rax, rdx
	jb 2281f
	jmp 2282f
2281:
	mov rdx, rax
2282:
2278:
	mov rax, QWORD PTR [rsp+152]
	test rax, rax
	je 2283f
	mov rcx, QWORD PTR [rsp+304]
	mov eax, 0
	mov QWORD PTR [rcx], rax
	mov QWORD PTR [rcx+24], rax
	mov rax, QWORD PTR [rsp+320]
	mov rcx, QWORD PTR [rsp+296]
	mov QWORD PTR [rcx], rax
	jmp 2284f
2283:
	mov rcx, QWORD PTR [rsp+304]
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rcx], rax
	mov QWORD PTR [rcx+24], rdx
	mov rax, QWORD PTR [rsp+320]
	mov rcx, QWORD PTR [rsp+296]
	mov QWORD PTR [rcx], rax
2284:
2274:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2285f
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [rsp+184], rax
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2287:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2287b
	jmp 2286f
2285:
	mov rsi, QWORD PTR [rsp+40]
	add rsi, 27008
	mov rdi, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+56]
	mov rdx, rcx
	shl rdx, 3
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
2288:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2288b
	mov eax, 1
2286:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 2
	je 2289f
	jmp 2290f
2289:
	mov eax, 3
2290:
	lea rsp, [rsp+296]
	lea rsp, [rsp+32]
	mov rbx, QWORD PTR [rsp]
	mov rbp, QWORD PTR [rsp+8]
	mov r12, QWORD PTR [rsp+16]
	mov r13, QWORD PTR [rsp+24]
	mov r14, QWORD PTR [rsp+32]
	mov r15, QWORD PTR [rsp+40]
	lea rsp, [rsp+48]
	ret
	.p2align 6
