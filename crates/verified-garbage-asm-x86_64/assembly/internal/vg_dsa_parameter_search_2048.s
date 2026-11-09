// The functions of `src/internal/vg_dsa_parameter_search_2048.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_parameter_search_2048:
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
	mov eax, 256
	mov QWORD PTR [rsp+136], rax
	mov eax, 32
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
	cmp rcx, 32
	jb 23f
	mov rcx, QWORD PTR [rsp+104]
	add rcx, rax
	mov QWORD PTR [rsp+8], rcx
	add rax, 32
	mov QWORD PTR [rsp+128], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25408
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rsp+216], rax
	mov eax, 32
	mov QWORD PTR [rsp+224], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
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
	mov r9d, 256
	call {vg_dsa_probable_prime}
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
	mov edx, 32
211:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 211b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 224
	mov ecx, 32
	mov edx, 256
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
	add rax, 1
	mov edx, 32
213:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 213b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 192
	mov ecx, 32
	mov edx, 256
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
	add rax, 2
	mov edx, 32
215:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 215b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 160
	mov ecx, 32
	mov edx, 256
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
	add rax, 3
	mov edx, 32
217:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 217b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 128
	mov ecx, 32
	mov edx, 256
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
218:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 218b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 4
	mov edx, 32
219:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 219b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 96
	mov ecx, 32
	mov edx, 256
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
220:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 220b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 5
	mov edx, 32
221:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 221b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 64
	mov ecx, 32
	mov edx, 256
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
222:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 222b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 6
	mov edx, 32
223:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 223b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 32
	mov ecx, 32
	mov edx, 256
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
224:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 224b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 7
	mov edx, 32
225:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 225b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 0
	mov ecx, 32
	mov edx, 256
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
226:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 226b
	mov rsi, QWORD PTR [rsp+32]
	add rsi, 0
	mov rdi, QWORD PTR [rsp]
	mov ecx, 256
	mov edx, 2048
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
227:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 227b
	movzx eax, BYTE PTR [r11-1]
	or rax, 1
	mov BYTE PTR [r11-1], al
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 28672
	mov r12d, 32
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
	mov eax, 272
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25024
	mov QWORD PTR [rdi+128], rax
	mov rax, 256
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25408
	mov QWORD PTR [rdi+144], rax
	mov rax, 32
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
228:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 228b
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
229:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 230f
	jmp 231f
230:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
231:
	test rdx, rdx
	jne 229b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
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
233:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 234f
	jmp 235f
234:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
235:
	test rdx, rdx
	jne 233b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
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
	mov rsi, rdi
	add rsi, 256
	mov rbx, r9
	add rbx, rbx
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
237:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 237b
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
238:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 238b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
239:
	mov ebp, 0
	mov rbx, rdi
	add rbx, 256
	mov r14, 0
240:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 240b
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
241:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 241b
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
242:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 242b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
243:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 243b
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
	jne 239b
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
244:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 244b
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
245:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 245b
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
246:
	mov rbp, rdx
	and rbp, 7
	je 247f
	jmp 248f
247:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
248:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 246b
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
249:
	mov rbp, rdx
	and rbp, 7
	je 250f
	jmp 251f
250:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
251:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 249b
	mov rsi, QWORD PTR [rdi+160]
	movzx eax, BYTE PTR [rsi]
	cmp rax, 128
	jb 252f
	mov rdi, QWORD PTR [rsp+40]
	mov esi, 5120
	mov rdx, QWORD PTR [rsp+104]
	add rdx, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+120]
	sub rcx, QWORD PTR [rsp+128]
	mov r8, rsp
	add r8, 152
	mov r9d, 2048
	call {vg_dsa_probable_prime}
	mov eax, eax
	test rax, rax
	je 254f
	mov rcx, QWORD PTR [rsp+152]
	add rcx, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+128], rcx
	jmp 255f
254:
255:
	mov rcx, rax
	shr rcx, 1
	add rax, rcx
	mov QWORD PTR [rsp+152], rax
	jmp 253f
252:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
253:
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 27840
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+16]
	cmp rax, 3
	je 256f
	jmp 257f
256:
	mov rax, QWORD PTR [rdi]
	add rax, 1
	mov QWORD PTR [rdi], rax
	mov rcx, QWORD PTR [rdi+8]
	add rcx, 8
	mov QWORD PTR [rdi+8], rcx
	cmp rax, 8192
	jb 258f
	mov eax, 2
	mov QWORD PTR [rdi+16], rax
	jmp 259f
258:
	mov eax, 3
	mov QWORD PTR [rdi+16], rax
259:
257:
	mov rax, QWORD PTR [rdi+16]
	cmp rax, 3
	je 210b
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 260f
	jmp 261f
260:
	mov rax, QWORD PTR [rsp+104]
	add rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+88], rax
	mov rcx, QWORD PTR [rsp+120]
	sub rcx, QWORD PTR [rsp+128]
	cmp rcx, 32768
	jb 262f
	mov eax, 32768
	mov QWORD PTR [rsp+96], rax
	jmp 263f
262:
	mov QWORD PTR [rsp+96], rcx
263:
	mov eax, 0
	mov QWORD PTR [rsp+160], rax
264:
	mov rcx, QWORD PTR [rsp+96]
	mov rax, QWORD PTR [rsp+160]
	sub rcx, rax
	cmp rcx, 256
	jb 265f
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+160]
	add rax, rcx
	add rcx, 256
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+160], rcx
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 28672
	mov r12d, 32
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
	mov eax, 272
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25472
	mov QWORD PTR [rdi+128], rax
	mov rax, 256
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 0
	mov QWORD PTR [rdi+144], rax
	mov rax, 256
	mov QWORD PTR [rdi+152], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
267:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 267b
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
268:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 269f
	jmp 270f
269:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
270:
	test rdx, rdx
	jne 268b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
271:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 271b
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
272:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 273f
	jmp 274f
273:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
274:
	test rdx, rdx
	jne 272b
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
275:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 275b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
276:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 276b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	test rax, rax
	je 277f
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
	mov eax, 256
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
279:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
280:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 281f
	jmp 282f
281:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
282:
	test rdx, rdx
	jne 280b
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
283:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 284f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 286f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 288f
290:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 290b
	jmp 289f
288:
289:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
291:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 291b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
292:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
293:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 293b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
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
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 292b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
296:
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
	je 297f
	mov eax, 0
	mov r14, 0
299:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 299b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2100:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2101:
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
	jne 2101b
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
2102:
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
	jne 2102b
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
	jne 2100b
	mov ebp, 0
	mov r14, 0
2103:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2104:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2104b
	jmp 298f
297:
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
2105:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2105b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2106:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2107:
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
	jne 2107b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2106b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2108:
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
	jne 2108b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2109:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2110:
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
	jne 2110b
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
	jne 2109b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2111:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2112:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2112b
298:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 296b
	jmp 287f
286:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2113:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2114:
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
	jne 2114b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2115:
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
2116:
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
	jne 2116b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2117:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2117b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2118:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2118b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2119:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2115b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2120:
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
	je 2121f
	mov eax, 0
	mov r14, 0
2123:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2124:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2125:
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
	jne 2125b
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
2126:
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
	jne 2126b
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
	jne 2124b
	mov ebp, 0
	mov r14, 0
2127:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2127b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2128:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2128b
	jmp 2122f
2121:
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
2129:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2129b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2130:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2131:
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
	jne 2131b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2130b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2132:
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
	jne 2132b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2133:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2134:
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
	jne 2134b
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
	jne 2133b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2135:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2135b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2136:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2136b
2122:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2120b
287:
	jmp 285f
284:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2137:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2137b
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
2138:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2139:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2139b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2140:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2140b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2141:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2141b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2138b
285:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2142:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2142b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2143:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2144f
	jmp 2145f
2144:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2145:
	test rdx, rdx
	jne 2143b
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
	je 2146f
	mov eax, 0
	mov r14, 0
2148:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2149:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2150:
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
	jne 2150b
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
2151:
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
	jne 2151b
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
	jne 2149b
	mov ebp, 0
	mov r14, 0
2152:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2152b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2153:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2153b
	jmp 2147f
2146:
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
2154:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2154b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2155:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2156:
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
	jne 2156b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2155b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2157:
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
	jne 2157b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2158:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2159:
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
	jne 2159b
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
	jne 2158b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2160:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2160b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2161:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2161b
2147:
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
	je 2162f
	mov eax, 0
	mov r14, 0
2164:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2164b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2165:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2166:
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
	jne 2166b
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
2167:
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
	jne 2167b
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
	jne 2165b
	mov ebp, 0
	mov r14, 0
2168:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2168b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2169:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2169b
	jmp 2163f
2162:
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
2170:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2170b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2171:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2172:
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
	jne 2172b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2171b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2173:
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
	jne 2173b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2174:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2175:
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
	jne 2175b
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
	jne 2174b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2176:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2176b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2177:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2177b
2163:
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
2178:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2178b
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
2179:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2179b
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
2180:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2180b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2181:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2181b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2182:
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
	je 2183f
	mov eax, 0
	mov r14, 0
2185:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2185b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2186:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2187:
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
	jne 2187b
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
2188:
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
	jne 2188b
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
	jne 2186b
	mov ebp, 0
	mov r14, 0
2189:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2189b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2190:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2190b
	jmp 2184f
2183:
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
2191:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2191b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2192:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2193:
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
	jne 2193b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2192b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2194:
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
	jne 2194b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2195:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2196:
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
	jne 2196b
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
	jne 2195b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2197:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2197b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2198:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2198b
2184:
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
2199:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2199b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2182b
2200:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2201:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2202:
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
	je 2203f
	mov eax, 0
	mov r14, 0
2205:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2205b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2206:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2207:
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
	jne 2207b
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
2208:
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
	jne 2208b
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
	jne 2206b
	mov ebp, 0
	mov r14, 0
2209:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2209b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2210:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2210b
	jmp 2204f
2203:
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
2211:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2211b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2212:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2213:
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
	jne 2213b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2212b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2214:
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
	jne 2214b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2215:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2216:
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
	jne 2216b
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
	jne 2215b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2217:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2217b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2218:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2218b
2204:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2202b
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
	je 2219f
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
2221:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2221b
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
	je 2222f
	mov eax, 0
	mov r14, 0
2224:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2224b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2225:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2226:
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
	jne 2226b
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
2227:
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
	jne 2227b
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
	jne 2225b
	mov ebp, 0
	mov r14, 0
2228:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2228b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2229:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2229b
	jmp 2223f
2222:
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
2230:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2230b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2231:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2232:
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
	jne 2232b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2231b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2233:
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
	jne 2233b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2234:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2235:
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
	jne 2235b
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
	jne 2234b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2236:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2236b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2237:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2237b
2223:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	jmp 2220f
2219:
2220:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2201b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2200b
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
	je 2238f
	mov eax, 0
	mov r14, 0
2240:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2240b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2241:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2242:
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
	jne 2242b
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
2243:
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
	jne 2243b
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
	jne 2241b
	mov ebp, 0
	mov r14, 0
2244:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2244b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2245:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2245b
	jmp 2239f
2238:
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
2246:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2246b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2247:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2248:
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
	jne 2248b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2247b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2249:
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
	jne 2249b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2250:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2251:
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
	jne 2251b
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
	jne 2250b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2252:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2252b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2253:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2253b
2239:
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
2254:
	mov rbp, rdx
	and rbp, 7
	je 2255f
	jmp 2256f
2255:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2256:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2254b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 28672
	mov r12d, 32
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
	mov eax, 272
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25472
	mov QWORD PTR [rdi+128], rax
	mov rax, 256
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 26240
	mov QWORD PTR [rdi+144], rax
	mov rax, 256
	mov QWORD PTR [rdi+152], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2257:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2257b
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
2258:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2259f
	jmp 2260f
2259:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2260:
	test rdx, rdx
	jne 2258b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2261:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2261b
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
2262:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2263f
	jmp 2264f
2263:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2264:
	test rdx, rdx
	jne 2262b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
2265:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2265b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
2266:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2266b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	test rax, rax
	je 2267f
	mov eax, 1
	mov QWORD PTR [rsp+152], rax
	jmp 2268f
2267:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
2268:
	jmp 278f
277:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
278:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 3
	jmp 266f
265:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
	mov eax, 1
	test rax, rax
266:
	je 264b
	mov rax, QWORD PTR [rsp+128]
	add rax, QWORD PTR [rsp+160]
	mov QWORD PTR [rsp+128], rax
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2269f
	mov rax, QWORD PTR [rsp+96]
	cmp rax, 32768
	jb 2271f
	jmp 2272f
2271:
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
2272:
	jmp 2270f
2269:
2270:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2273f
	jmp 2274f
2273:
	mov rsi, QWORD PTR [rsp+40]
	mov rdi, rsi
	add rsi, 25472
	add rdi, 27008
	mov ecx, 256
	mov edx, 2048
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
2275:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2275b
	mov rsi, QWORD PTR [rsp+40]
	mov rdi, rsi
	add rsi, 25408
	add rdi, 27264
	mov ecx, 32
	mov edx, 256
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
2276:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2276b
	mov rsi, QWORD PTR [rsp+40]
	mov rdi, rsi
	add rsi, 26240
	add rdi, 27296
	mov ecx, 256
	mov edx, 2048
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
2277:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2277b
	mov rdi, QWORD PTR [rsp+40]
	mov r8, rdi
	add rdi, 27008
	add r8, 40960
	mov edx, 256
	mov ecx, 32
	mov esi, 544
	mov r9d, 4096
	call {vg_dsa_generation_check_parameters}
	test rax, rax
	je 2278f
	mov eax, 1
	mov QWORD PTR [rsp+152], rax
	jmp 2279f
2278:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
2279:
2274:
261:
29:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 3
	je 2280f
	jmp 2281f
2280:
	mov rax, QWORD PTR [rsp+312]
	sub rax, 1
	mov QWORD PTR [rsp+312], rax
2281:
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
	je 2282f
	mov rcx, QWORD PTR [rsp+304]
	mov eax, 0
	mov QWORD PTR [rcx], rax
	mov QWORD PTR [rcx+24], rax
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2284f
	mov rax, QWORD PTR [rsp+320]
	mov rcx, QWORD PTR [rsp+296]
	mov QWORD PTR [rcx], rax
	jmp 2285f
2284:
	mov rax, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+296]
	mov QWORD PTR [rcx], rax
2285:
	jmp 2283f
2282:
	mov rcx, QWORD PTR [rsp+120]
	sub rcx, QWORD PTR [rsp+320]
	mov edx, 8388864
	cmp rcx, rdx
	jb 2286f
	mov eax, 2
	mov QWORD PTR [rsp+152], rax
	jmp 2287f
2286:
	mov eax, 65536
	cmp rcx, rax
	jb 2288f
	mov rax, rcx
	jmp 2289f
2288:
2289:
	add rax, rax
	cmp rax, rdx
	jb 2290f
	jmp 2291f
2290:
	mov rdx, rax
2291:
2287:
	mov rax, QWORD PTR [rsp+152]
	test rax, rax
	je 2292f
	mov rcx, QWORD PTR [rsp+304]
	mov eax, 0
	mov QWORD PTR [rcx], rax
	mov QWORD PTR [rcx+24], rax
	mov rax, QWORD PTR [rsp+320]
	mov rcx, QWORD PTR [rsp+296]
	mov QWORD PTR [rcx], rax
	jmp 2293f
2292:
	mov rcx, QWORD PTR [rsp+304]
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rcx], rax
	mov QWORD PTR [rcx+24], rdx
	mov rax, QWORD PTR [rsp+320]
	mov rcx, QWORD PTR [rsp+296]
	mov QWORD PTR [rcx], rax
2293:
2283:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2294f
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [rsp+184], rax
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2296:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2296b
	jmp 2295f
2294:
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
2297:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2297b
	mov eax, 1
2295:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 2
	je 2298f
	jmp 2299f
2298:
	mov eax, 3
2299:
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
