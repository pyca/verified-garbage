// The functions of `src/internal/vg_dsa_generation_3072_sha256_avx2_mr_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_generation_3072_sha256_avx2_mr_adx:
	lea rsp, [rsp-48]
	mov QWORD PTR [rsp], rbx
	mov QWORD PTR [rsp+8], rbp
	mov QWORD PTR [rsp+16], r12
	mov QWORD PTR [rsp+24], r13
	mov QWORD PTR [rsp+32], r14
	mov QWORD PTR [rsp+40], r15
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+48], rdi
	mov QWORD PTR [rsp+56], rsi
	mov QWORD PTR [rsp+136], rdx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+64], r8
	mov QWORD PTR [rsp+72], r9
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+120], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+40], rax
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
	mov rax, QWORD PTR [rsp+136]
	cmp rax, 128
	je 20f
	cmp rax, 256
	je 22f
	mov eax, 0
	mov QWORD PTR [rsp+80], rax
24:
	mov rcx, QWORD PTR [rsp+72]
	mov rax, QWORD PTR [rsp+80]
	sub rcx, rax
	cmp rcx, 32
	jb 25f
	mov rax, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp+80]
	add rax, rcx
	add rcx, 32
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+80], rcx
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
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
27:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 27b
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
	call {vg_dsa_probable_prime_adx}
	mov eax, eax
	test rax, rax
	je 28f
	mov rcx, QWORD PTR [rsp+152]
	add rcx, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+128], rcx
	jmp 29f
28:
29:
	mov rcx, rax
	shr rcx, 1
	add rax, rcx
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 210f
	jmp 211f
210:
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 27840
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov eax, 1
	mov QWORD PTR [rdi+8], rax
212:
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 352
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
	add rax, 1
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 320
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
	add rax, 2
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 288
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
	add rax, 3
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rdi, QWORD PTR [rsp+32]
	add rdi, 256
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
	add rax, 4
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
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
	add rax, 5
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
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
	add rax, 6
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
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
226:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 226b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 7
	mov edx, 32
227:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 227b
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
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
228:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 228b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 8
	mov edx, 32
229:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 229b
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
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
230:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 230b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 9
	mov edx, 32
231:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 231b
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
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
232:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 232b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 10
	mov edx, 32
233:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 233b
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
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
234:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 234b
	mov rsi, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+16]
	add rax, 11
	mov edx, 32
235:
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	add rax, rcx
	mov BYTE PTR [rdi+rdx*1-1], al
	shr rax, 8
	sub rdx, 1
	jne 235b
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
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
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
236:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 236b
	mov rsi, QWORD PTR [rsp+32]
	add rsi, 0
	mov rdi, QWORD PTR [rsp]
	mov ecx, 384
	mov edx, 3072
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
237:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 237b
	movzx eax, BYTE PTR [r11-1]
	or rax, 1
	mov BYTE PTR [r11-1], al
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 28672
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
	mov eax, 400
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25024
	mov QWORD PTR [rdi+128], rax
	mov rax, 384
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
238:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 238b
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
239:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 240f
	jmp 241f
240:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
241:
	test rdx, rdx
	jne 239b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, r8
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
242:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 242b
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
243:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 244f
	jmp 245f
244:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
245:
	test rdx, rdx
	jne 243b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov ebp, 0
	mov rbx, r9
	add rbx, rbx
	add rbx, rdi
	add rbx, 256
	mov r14, 0
246:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 246b
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
247:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 247b
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
248:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 248b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
249:
	mov ebp, 0
	mov rbx, rdi
	add rbx, 256
	mov r14, 0
250:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 250b
	mov rbx, r9
	add rbx, rdi
	add rbx, 256
	add r12, 1
	mov r14, 0
251:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 251b
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
252:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 252b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	mov QWORD PTR [rsi+r12*8], rax
	sbb rbp, rbp
	add r12, 1
	mov r14, 0
253:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 253b
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
	jne 249b
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
254:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 254b
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
255:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 255b
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
256:
	mov rbp, rdx
	and rbp, 7
	je 257f
	jmp 258f
257:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
258:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 256b
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
259:
	mov rbp, rdx
	and rbp, 7
	je 260f
	jmp 261f
260:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
261:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 259b
	mov rsi, QWORD PTR [rdi+160]
	movzx eax, BYTE PTR [rsi]
	cmp rax, 128
	jb 262f
	mov rdi, QWORD PTR [rsp+40]
	mov esi, 5120
	mov rdx, QWORD PTR [rsp+104]
	add rdx, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+120]
	sub rcx, QWORD PTR [rsp+128]
	mov r8, rsp
	add r8, 152
	mov r9d, 3072
	call {vg_dsa_probable_prime_adx}
	mov eax, eax
	test rax, rax
	je 264f
	mov rcx, QWORD PTR [rsp+152]
	add rcx, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+128], rcx
	jmp 265f
264:
265:
	mov rcx, rax
	shr rcx, 1
	add rax, rcx
	mov QWORD PTR [rsp+152], rax
	jmp 263f
262:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
263:
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 27840
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+16]
	cmp rax, 3
	je 266f
	jmp 267f
266:
	mov rax, QWORD PTR [rdi]
	add rax, 1
	mov QWORD PTR [rdi], rax
	mov rcx, QWORD PTR [rdi+8]
	add rcx, 12
	mov QWORD PTR [rdi+8], rcx
	cmp rax, 12288
	jb 268f
	mov eax, 2
	mov QWORD PTR [rdi+16], rax
	jmp 269f
268:
	mov eax, 3
	mov QWORD PTR [rdi+16], rax
269:
267:
	mov rax, QWORD PTR [rdi+16]
	cmp rax, 3
	je 212b
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 270f
	jmp 271f
270:
	mov eax, 0
	mov QWORD PTR [rsp+160], rax
272:
	mov rcx, QWORD PTR [rsp+96]
	mov rax, QWORD PTR [rsp+160]
	sub rcx, rax
	cmp rcx, 384
	jb 273f
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+160]
	add rax, rcx
	add rcx, 384
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+160], rcx
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 28672
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
	mov eax, 400
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25472
	mov QWORD PTR [rdi+128], rax
	mov rax, 384
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 0
	mov QWORD PTR [rdi+144], rax
	mov rax, 384
	mov QWORD PTR [rdi+152], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
275:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 275b
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
276:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 277f
	jmp 278f
277:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
278:
	test rdx, rdx
	jne 276b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
279:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 279b
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
283:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 283b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
284:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 284b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	test rax, rax
	je 285f
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
	mov eax, 384
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
287:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 287b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
288:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 289f
	jmp 290f
289:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
290:
	test rdx, rdx
	jne 288b
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
291:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 291b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 292f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 294f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 296f
298:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 298b
	jmp 297f
296:
297:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
299:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 299b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2100:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2101:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2101b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
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
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2100b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2104:
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
	je 2105f
	mov eax, 0
	mov r14, 0
2107:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2108:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2109:
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
	jne 2109b
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
2110:
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
	jne 2110b
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
	jne 2108b
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
	jmp 2106f
2105:
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
2113:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2113b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2114:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2115:
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
	jne 2115b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2114b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2116:
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
	jne 2116b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2117:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2118:
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
	jne 2118b
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
	jne 2117b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2119:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2120:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2120b
2106:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2104b
	jmp 295f
294:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2121:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2122:
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
	jne 2122b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2123:
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
2124:
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
	jne 2124b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2125:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2125b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2126:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2126b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2127:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2127b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2123b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2128:
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
	je 2129f
	mov eax, 0
	mov r14, 0
2131:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2131b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2132:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2133:
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
	jne 2133b
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
2134:
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
	jne 2134b
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
	jne 2132b
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
	jmp 2130f
2129:
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
2137:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2137b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2138:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2139:
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
	jne 2139b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2138b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2140:
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
	jne 2140b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2141:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2142:
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
	jne 2142b
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
	jne 2141b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
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
2130:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2128b
295:
	jmp 293f
292:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2145:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2145b
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
2146:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2147:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2147b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2148:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2148b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2149:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2149b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2146b
293:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2150:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2150b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
2151:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2152f
	jmp 2153f
2152:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2153:
	test rdx, rdx
	jne 2151b
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
	je 2154f
	mov eax, 0
	mov r14, 0
2156:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2156b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2157:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2158:
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
	jne 2158b
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
2159:
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
	jne 2159b
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
	jne 2157b
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
	jmp 2155f
2154:
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
2162:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2162b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2163:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2164:
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
	jne 2164b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2163b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2165:
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
	jne 2165b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2166:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2167:
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
	jne 2167b
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
	jne 2166b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
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
2155:
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
	je 2170f
	mov eax, 0
	mov r14, 0
2172:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2172b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2173:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2174:
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
	jne 2174b
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
2175:
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
	jne 2175b
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
	jne 2173b
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
	jmp 2171f
2170:
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
2178:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2178b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2179:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2180:
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
	jne 2180b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2179b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2181:
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
	jne 2181b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2182:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2183:
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
	jne 2183b
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
	jne 2182b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2184:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2184b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2185:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2185b
2171:
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
2186:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2186b
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
2187:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2187b
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
2188:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2188b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
2189:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2189b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
2190:
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
	je 2191f
	mov eax, 0
	mov r14, 0
2193:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2193b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2194:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2195:
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
	jne 2195b
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
2196:
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
	jne 2196b
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
	jne 2194b
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
	jmp 2192f
2191:
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
2199:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2199b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2200:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2201:
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
	jne 2201b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2200b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2202:
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
	jne 2202b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2203:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
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
	jne 2203b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2205:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2205b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2206:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2206b
2192:
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
2207:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2207b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2190b
2208:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
2209:
	mov eax, 4
	mov QWORD PTR [rdi+216], rax
2210:
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
	je 2211f
	mov eax, 0
	mov r14, 0
2213:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2213b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2214:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2215:
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
	jne 2215b
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
2216:
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
	jne 2216b
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
	jne 2214b
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
	jmp 2212f
2211:
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
2219:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2219b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2220:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2221:
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
	jne 2221b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2220b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2222:
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
	jne 2222b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2223:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2224:
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
	jne 2224b
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
	jne 2223b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2225:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2225b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2226:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2226b
2212:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	mov rax, QWORD PTR [rdi+216]
	sub rax, 1
	mov QWORD PTR [rdi+216], rax
	jne 2210b
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
	je 2227f
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
2229:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2229b
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
	je 2230f
	mov eax, 0
	mov r14, 0
2232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2233:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2234:
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
	jne 2234b
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
2235:
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
	jne 2235b
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
	jne 2233b
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
	jmp 2231f
2230:
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
2238:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2238b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2239:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2240:
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
	jne 2240b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2239b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2241:
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
	jne 2241b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2242:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2243:
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
	jne 2243b
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
	jne 2242b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
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
2231:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	jmp 2228f
2227:
2228:
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 2209b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 2208b
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
	je 2246f
	mov eax, 0
	mov r14, 0
2248:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2248b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
2249:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
2250:
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
	jne 2250b
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
2251:
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
	jne 2251b
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
	jne 2249b
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
	jmp 2247f
2246:
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
2254:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 2254b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
2255:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2256:
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
	jne 2256b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 2255b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
2257:
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
	jne 2257b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
2258:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
2259:
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
	jne 2259b
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
	jne 2258b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
2260:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2260b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2261:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2261b
2247:
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
2262:
	mov rbp, rdx
	and rbp, 7
	je 2263f
	jmp 2264f
2263:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2264:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2262b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rsp+40]
	add rdi, 28672
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
	mov eax, 400
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 25472
	mov QWORD PTR [rdi+128], rax
	mov rax, 384
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsp+40]
	add rax, 26240
	mov QWORD PTR [rdi+144], rax
	mov rax, 384
	mov QWORD PTR [rdi+152], rax
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2265:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2265b
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
2266:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2267f
	jmp 2268f
2267:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2268:
	test rdx, rdx
	jne 2266b
	mov r12, QWORD PTR [rdi+48]
	mov r9, QWORD PTR [rdi+224]
	mov r8, r9
	add r8, rdi
	add r8, 256
	mov eax, 0
	mov r14, 0
2269:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2269b
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
2270:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 2271f
	jmp 2272f
2271:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
2272:
	test rdx, rdx
	jne 2270b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
2273:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2273b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
2274:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 2274b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	test rax, rax
	je 2275f
	mov eax, 1
	mov QWORD PTR [rsp+152], rax
	jmp 2276f
2275:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
2276:
	jmp 286f
285:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
286:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 3
	jmp 274f
273:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
	mov eax, 1
	test rax, rax
274:
	je 272b
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2277f
	jmp 2278f
2277:
	mov rsi, QWORD PTR [rsp+40]
	mov rdi, rsi
	add rsi, 25472
	add rdi, 27008
	mov ecx, 384
	mov edx, 3072
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
2279:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2279b
	mov rsi, QWORD PTR [rsp+40]
	mov rdi, rsi
	add rsi, 25408
	add rdi, 27392
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
2280:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2280b
	mov rsi, QWORD PTR [rsp+40]
	mov rdi, rsi
	add rsi, 26240
	add rdi, 27424
	mov ecx, 384
	mov edx, 3072
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
2281:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2281b
	mov rdi, QWORD PTR [rsp+40]
	mov r8, rdi
	add rdi, 27008
	add r8, 40960
	mov edx, 384
	mov ecx, 32
	mov esi, 800
	mov r9d, 6144
	call {vg_dsa_generation_check_parameters}
	test rax, rax
	je 2282f
	mov eax, 1
	mov QWORD PTR [rsp+152], rax
	jmp 2283f
2282:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
2283:
2278:
271:
211:
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 3
	jmp 26f
25:
	mov eax, 3
	mov QWORD PTR [rsp+152], rax
	mov eax, 1
	test rax, rax
26:
	je 24b
	mov rax, QWORD PTR [rsp+152]
	cmp rax, 1
	je 2284f
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+56]
	mov QWORD PTR [rsp+184], rax
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2286:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2286b
	jmp 2285f
2284:
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
2287:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 2287b
	mov eax, 1
2285:
	jmp 23f
22:
23:
	jmp 21f
20:
21:
	lea rsp, [rsp+296]
	mov rbx, QWORD PTR [rsp]
	mov rbp, QWORD PTR [rsp+8]
	mov r12, QWORD PTR [rsp+16]
	mov r13, QWORD PTR [rsp+24]
	mov r14, QWORD PTR [rsp+32]
	mov r15, QWORD PTR [rsp+40]
	lea rsp, [rsp+48]
	ret
	.p2align 6
