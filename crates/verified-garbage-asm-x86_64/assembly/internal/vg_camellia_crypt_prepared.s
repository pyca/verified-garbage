// The functions of `src/internal/vg_camellia_crypt_prepared.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_crypt_prepared:
	mov r9, rsi
	mov QWORD PTR [r9+2968], rbx
	mov QWORD PTR [r9+2976], rbp
	mov QWORD PTR [r9+2984], r12
	mov QWORD PTR [r9+2992], r13
	mov QWORD PTR [r9+3000], r14
	mov QWORD PTR [r9+3008], r15
	cmp rdi, 18
	je 20f
	mov rdi, r9
	add rdi, 2816
	jmp 21f
20:
	mov rdi, r9
	add rdi, 2304
21:
	mov QWORD PTR [r9+2944], rdi
	mov rdx, r9
	add rdx, 3016
	mov rsi, r9
	add rsi, 768
	mov rax, QWORD PTR [rdx+8]
	mov rbx, QWORD PTR [rdx+24]
	mov rcx, QWORD PTR [rdx+40]
	mov rbp, QWORD PTR [rdx+56]
	mov r10, QWORD PTR [rdx+72]
	mov r11, QWORD PTR [rdx+88]
	mov r12, QWORD PTR [rdx+104]
	mov r13, QWORD PTR [rdx+120]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [r9+576], rax
	mov QWORD PTR [r9+584], rbx
	mov QWORD PTR [r9+592], rcx
	mov QWORD PTR [r9+600], rbp
	mov QWORD PTR [r9+608], r10
	mov QWORD PTR [r9+616], r11
	mov QWORD PTR [r9+624], r12
	mov QWORD PTR [r9+632], r13
	mov rax, QWORD PTR [rdx]
	mov rbx, QWORD PTR [rdx+16]
	mov rcx, QWORD PTR [rdx+32]
	mov rbp, QWORD PTR [rdx+48]
	mov r10, QWORD PTR [rdx+64]
	mov r11, QWORD PTR [rdx+80]
	mov r12, QWORD PTR [rdx+96]
	mov r13, QWORD PTR [rdx+112]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	mov QWORD PTR [r9+512], rax
	mov QWORD PTR [r9+520], rbx
	mov QWORD PTR [r9+528], rcx
	mov QWORD PTR [r9+536], rbp
	mov QWORD PTR [r9+544], r10
	mov QWORD PTR [r9+552], r11
	mov QWORD PTR [r9+560], r12
	mov QWORD PTR [r9+568], r13
	mov r14, QWORD PTR [r9+576]
	xor r14, QWORD PTR [rsi+64]
	mov QWORD PTR [r9+576], r14
	mov r14, QWORD PTR [r9+584]
	xor r14, QWORD PTR [rsi+72]
	mov QWORD PTR [r9+584], r14
	mov r14, QWORD PTR [r9+592]
	xor r14, QWORD PTR [rsi+80]
	mov QWORD PTR [r9+592], r14
	mov r14, QWORD PTR [r9+600]
	xor r14, QWORD PTR [rsi+88]
	mov QWORD PTR [r9+600], r14
	mov r14, QWORD PTR [r9+608]
	xor r14, QWORD PTR [rsi+96]
	mov QWORD PTR [r9+608], r14
	mov r14, QWORD PTR [r9+616]
	xor r14, QWORD PTR [rsi+104]
	mov QWORD PTR [r9+616], r14
	mov r14, QWORD PTR [r9+624]
	xor r14, QWORD PTR [rsi+112]
	mov QWORD PTR [r9+624], r14
	mov r14, QWORD PTR [r9+632]
	xor r14, QWORD PTR [rsi+120]
	mov QWORD PTR [r9+632], r14
	add rsi, 128
22:
	mov rdi, rsi
	add rdi, 384
23:
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r13
	xor r14, rbx
	mov r15, r11
	xor r15, rbp
	mov QWORD PTR [r9+8], r11
	mov r11, rcx
	xor r11, r14
	mov QWORD PTR [r9+16], r14
	mov r14, r12
	xor r14, rax
	mov QWORD PTR [r9+24], rbp
	mov rbp, rax
	xor rbp, r15
	mov QWORD PTR [r9+32], rbp
	mov rbp, r10
	xor rbp, rbx
	mov QWORD PTR [r9+40], rbp
	mov rbp, r10
	xor rbp, r11
	mov QWORD PTR [r9+48], rbp
	mov rbp, r12
	xor rbp, r15
	mov QWORD PTR [r9+56], r15
	mov r15, rcx
	xor r15, r14
	mov QWORD PTR [r9+64], r15
	mov r15, r11
	xor r15, r14
	mov QWORD PTR [r9+72], r15
	mov r15, r13
	xor r15, r12
	mov QWORD PTR [r9+80], rbp
	mov rbp, r13
	xor rbp, r14
	xor rbp, QWORD PTR [r9]
	mov QWORD PTR [r9+88], rbp
	mov rbp, r12
	xor rbp, QWORD PTR [r9+24]
	mov QWORD PTR [r9+96], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, rbx
	mov QWORD PTR [r9+104], r12
	mov r12, QWORD PTR [r9+8]
	xor r12, rax
	mov QWORD PTR [r9+112], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, r11
	xor r14, r10
	xor r10, r15
	xor rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9]
	mov r15, rcx
	xor r15, QWORD PTR [r9+32]
	xor rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+80]
	xor r14, QWORD PTR [r9]
	mov QWORD PTR [r9+8], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov QWORD PTR [r9+120], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+40]
	mov QWORD PTR [r9+16], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+48]
	mov QWORD PTR [r9+128], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+72]
	mov QWORD PTR [r9+56], r14
	mov r14, r11
	xor r14, QWORD PTR [r9+32]
	xor r14, QWORD PTR [r9]
	xor r11, rbp
	xor r11, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+40]
	xor rbp, QWORD PTR [r9]
	xor r12, QWORD PTR [r9+48]
	xor r12, QWORD PTR [r9]
	mov QWORD PTR [r9+40], r11
	mov r11, QWORD PTR [r9+64]
	xor r11, QWORD PTR [r9+112]
	xor r11, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [r9+96]
	xor rax, QWORD PTR [r9+104]
	xor rax, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9]
	mov QWORD PTR [r9+96], rbx
	mov rbx, rcx
	and rbx, r10
	mov QWORD PTR [r9+104], rcx
	mov rcx, rax
	and rcx, r11
	xor rcx, rbx
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [r9+48]
	and rax, r12
	xor rax, rbx
	mov rbx, r15
	and rbx, r14
	mov QWORD PTR [r9+32], r15
	mov r15, QWORD PTR [r9+16]
	and r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+136], r13
	mov r13, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+80]
	xor r13, rbx
	mov rbx, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+128]
	mov QWORD PTR [r9+144], r14
	mov r14, rbp
	and r14, QWORD PTR [r9+64]
	xor r14, rbx
	mov QWORD PTR [r9+152], rbp
	mov rbp, QWORD PTR [r9+8]
	and rbp, QWORD PTR [r9+88]
	xor rbp, rbx
	xor rcx, r14
	xor rax, rbp
	xor r15, r14
	xor r13, rbp
	xor rcx, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+120]
	xor r15, QWORD PTR [r9+96]
	xor r13, QWORD PTR [r9+40]
	mov rbp, rcx
	xor rbp, rax
	and rcx, r15
	mov r14, r13
	xor r14, rcx
	mov rbx, rbp
	and rbx, r14
	xor rbx, rax
	mov QWORD PTR [r9+40], r12
	mov r12, r15
	xor r12, r13
	xor rax, rcx
	and rax, r12
	xor rax, r13
	xor r15, rax
	mov r12, r14
	xor r12, rax
	and r13, r12
	xor r15, r13
	xor r14, r13
	and r14, rbx
	xor rbp, r14
	mov r14, rbp
	xor r14, r15
	mov r13, rbx
	xor r13, rax
	mov r12, rbx
	xor r12, rbp
	mov rcx, rax
	xor rcx, r15
	mov QWORD PTR [r9+96], rbx
	mov rbx, r13
	xor rbx, r14
	and r10, rcx
	and r11, r15
	mov QWORD PTR [r9+120], r10
	mov r10, rax
	and r10, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r10
	mov r10, r12
	and r10, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], r10
	mov r10, rbp
	and r10, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], r10
	mov r10, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, r13
	and r10, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r10
	mov r10, rbx
	and r10, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r10
	mov r10, r14
	and r10, QWORD PTR [r9+88]
	and rcx, QWORD PTR [r9+104]
	and r15, QWORD PTR [r9+112]
	and rax, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	and rbp, QWORD PTR [r9+16]
	mov QWORD PTR [r9+16], rbp
	mov rbp, QWORD PTR [r9+96]
	and rbp, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+152]
	and r14, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], r15
	mov r15, r11
	xor r15, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r11
	mov r11, QWORD PTR [r9+144]
	xor r11, QWORD PTR [r9+80]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+128]
	xor rcx, r10
	mov QWORD PTR [r9+152], r10
	mov r10, QWORD PTR [r9+120]
	xor r10, rbx
	xor rax, r15
	mov QWORD PTR [r9+24], r15
	mov r15, r12
	xor r15, r11
	mov QWORD PTR [r9+72], r11
	mov r11, r13
	xor r11, rcx
	xor rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+96], rbp
	mov rbp, QWORD PTR [r9+128]
	xor rbp, r14
	mov QWORD PTR [r9+128], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+144]
	mov QWORD PTR [r9+152], rcx
	mov rcx, QWORD PTR [r9+144]
	xor rcx, QWORD PTR [r9+8]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+16]
	xor rcx, r15
	xor rbx, r11
	mov QWORD PTR [r9+16], rbx
	mov rbx, r10
	xor rbx, rax
	mov QWORD PTR [r9+32], rbx
	mov rbx, QWORD PTR [r9+120]
	xor rbx, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], rcx
	mov rcx, QWORD PTR [r9+64]
	xor rcx, QWORD PTR [r9+136]
	xor r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, QWORD PTR [r9+8]
	xor r10, rbp
	xor r12, rax
	xor r13, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+152]
	mov rax, QWORD PTR [r9+72]
	xor rax, QWORD PTR [r9+144]
	xor rbx, QWORD PTR [r9+128]
	xor r15, QWORD PTR [r9+96]
	xor r11, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rbx
	mov rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9+152]
	xor rbp, r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+16]
	mov QWORD PTR [r9+152], r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+32]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9]
	xor r10, QWORD PTR [r9+32]
	xor r10, QWORD PTR [r9]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rbx
	xor r12, QWORD PTR [r9]
	xor r14, r13
	xor r14, QWORD PTR [r9]
	xor r15, rbp
	xor r11, rcx
	xor r11, QWORD PTR [r9]
	mov r13, r15
	mov QWORD PTR [r9+80], r12
	mov r12, r11
	mov r11, rax
	mov QWORD PTR [r9+32], r10
	mov r10, QWORD PTR [r9+144]
	mov rbp, QWORD PTR [r9+80]
	mov rcx, QWORD PTR [r9+32]
	mov rbx, r14
	mov rax, QWORD PTR [r9+152]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+408]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+408]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+408]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+408]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+408]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+408]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+408]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+408]
	xor rax, r14
	mov r15, rax
	mov r14, rax
	xor r14, rbx
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov r14, rbx
	xor r14, rcx
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	mov r14, rcx
	xor r14, rbp
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	mov r14, rbp
	xor r14, r10
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	mov r14, r10
	xor r14, r11
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	mov r14, r11
	xor r14, r12
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	mov r14, r12
	xor r14, r13
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	mov r14, r13
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	xor r13, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	xor rax, QWORD PTR [r9+576]
	mov QWORD PTR [r9+576], rax
	xor rbx, QWORD PTR [r9+584]
	mov QWORD PTR [r9+584], rbx
	xor rcx, QWORD PTR [r9+592]
	mov QWORD PTR [r9+592], rcx
	xor rbp, QWORD PTR [r9+600]
	mov QWORD PTR [r9+600], rbp
	xor r10, QWORD PTR [r9+608]
	mov QWORD PTR [r9+608], r10
	xor r11, QWORD PTR [r9+616]
	mov QWORD PTR [r9+616], r11
	xor r12, QWORD PTR [r9+624]
	mov QWORD PTR [r9+624], r12
	xor r13, QWORD PTR [r9+632]
	mov QWORD PTR [r9+632], r13
	xor rax, QWORD PTR [rsi+64]
	xor rbx, QWORD PTR [rsi+72]
	xor rcx, QWORD PTR [rsi+80]
	xor rbp, QWORD PTR [rsi+88]
	xor r10, QWORD PTR [rsi+96]
	xor r11, QWORD PTR [rsi+104]
	xor r12, QWORD PTR [rsi+112]
	xor r13, QWORD PTR [rsi+120]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r13
	xor r14, rbx
	mov r15, r11
	xor r15, rbp
	mov QWORD PTR [r9+8], r11
	mov r11, rcx
	xor r11, r14
	mov QWORD PTR [r9+16], r14
	mov r14, r12
	xor r14, rax
	mov QWORD PTR [r9+24], rbp
	mov rbp, rax
	xor rbp, r15
	mov QWORD PTR [r9+32], rbp
	mov rbp, r10
	xor rbp, rbx
	mov QWORD PTR [r9+40], rbp
	mov rbp, r10
	xor rbp, r11
	mov QWORD PTR [r9+48], rbp
	mov rbp, r12
	xor rbp, r15
	mov QWORD PTR [r9+56], r15
	mov r15, rcx
	xor r15, r14
	mov QWORD PTR [r9+64], r15
	mov r15, r11
	xor r15, r14
	mov QWORD PTR [r9+72], r15
	mov r15, r13
	xor r15, r12
	mov QWORD PTR [r9+80], rbp
	mov rbp, r13
	xor rbp, r14
	xor rbp, QWORD PTR [r9]
	mov QWORD PTR [r9+88], rbp
	mov rbp, r12
	xor rbp, QWORD PTR [r9+24]
	mov QWORD PTR [r9+96], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, rbx
	mov QWORD PTR [r9+104], r12
	mov r12, QWORD PTR [r9+8]
	xor r12, rax
	mov QWORD PTR [r9+112], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, r11
	xor r14, r10
	xor r10, r15
	xor rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9]
	mov r15, rcx
	xor r15, QWORD PTR [r9+32]
	xor rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+80]
	xor r14, QWORD PTR [r9]
	mov QWORD PTR [r9+8], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov QWORD PTR [r9+120], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+40]
	mov QWORD PTR [r9+16], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+48]
	mov QWORD PTR [r9+128], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+72]
	mov QWORD PTR [r9+56], r14
	mov r14, r11
	xor r14, QWORD PTR [r9+32]
	xor r14, QWORD PTR [r9]
	xor r11, rbp
	xor r11, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+40]
	xor rbp, QWORD PTR [r9]
	xor r12, QWORD PTR [r9+48]
	xor r12, QWORD PTR [r9]
	mov QWORD PTR [r9+40], r11
	mov r11, QWORD PTR [r9+64]
	xor r11, QWORD PTR [r9+112]
	xor r11, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [r9+96]
	xor rax, QWORD PTR [r9+104]
	xor rax, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9]
	mov QWORD PTR [r9+96], rbx
	mov rbx, rcx
	and rbx, r10
	mov QWORD PTR [r9+104], rcx
	mov rcx, rax
	and rcx, r11
	xor rcx, rbx
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [r9+48]
	and rax, r12
	xor rax, rbx
	mov rbx, r15
	and rbx, r14
	mov QWORD PTR [r9+32], r15
	mov r15, QWORD PTR [r9+16]
	and r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+136], r13
	mov r13, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+80]
	xor r13, rbx
	mov rbx, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+128]
	mov QWORD PTR [r9+144], r14
	mov r14, rbp
	and r14, QWORD PTR [r9+64]
	xor r14, rbx
	mov QWORD PTR [r9+152], rbp
	mov rbp, QWORD PTR [r9+8]
	and rbp, QWORD PTR [r9+88]
	xor rbp, rbx
	xor rcx, r14
	xor rax, rbp
	xor r15, r14
	xor r13, rbp
	xor rcx, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+120]
	xor r15, QWORD PTR [r9+96]
	xor r13, QWORD PTR [r9+40]
	mov rbp, rcx
	xor rbp, rax
	and rcx, r15
	mov r14, r13
	xor r14, rcx
	mov rbx, rbp
	and rbx, r14
	xor rbx, rax
	mov QWORD PTR [r9+40], r12
	mov r12, r15
	xor r12, r13
	xor rax, rcx
	and rax, r12
	xor rax, r13
	xor r15, rax
	mov r12, r14
	xor r12, rax
	and r13, r12
	xor r15, r13
	xor r14, r13
	and r14, rbx
	xor rbp, r14
	mov r14, rbp
	xor r14, r15
	mov r13, rbx
	xor r13, rax
	mov r12, rbx
	xor r12, rbp
	mov rcx, rax
	xor rcx, r15
	mov QWORD PTR [r9+96], rbx
	mov rbx, r13
	xor rbx, r14
	and r10, rcx
	and r11, r15
	mov QWORD PTR [r9+120], r10
	mov r10, rax
	and r10, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r10
	mov r10, r12
	and r10, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], r10
	mov r10, rbp
	and r10, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], r10
	mov r10, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, r13
	and r10, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r10
	mov r10, rbx
	and r10, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r10
	mov r10, r14
	and r10, QWORD PTR [r9+88]
	and rcx, QWORD PTR [r9+104]
	and r15, QWORD PTR [r9+112]
	and rax, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	and rbp, QWORD PTR [r9+16]
	mov QWORD PTR [r9+16], rbp
	mov rbp, QWORD PTR [r9+96]
	and rbp, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+152]
	and r14, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], r15
	mov r15, r11
	xor r15, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r11
	mov r11, QWORD PTR [r9+144]
	xor r11, QWORD PTR [r9+80]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+128]
	xor rcx, r10
	mov QWORD PTR [r9+152], r10
	mov r10, QWORD PTR [r9+120]
	xor r10, rbx
	xor rax, r15
	mov QWORD PTR [r9+24], r15
	mov r15, r12
	xor r15, r11
	mov QWORD PTR [r9+72], r11
	mov r11, r13
	xor r11, rcx
	xor rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+96], rbp
	mov rbp, QWORD PTR [r9+128]
	xor rbp, r14
	mov QWORD PTR [r9+128], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+144]
	mov QWORD PTR [r9+152], rcx
	mov rcx, QWORD PTR [r9+144]
	xor rcx, QWORD PTR [r9+8]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+16]
	xor rcx, r15
	xor rbx, r11
	mov QWORD PTR [r9+16], rbx
	mov rbx, r10
	xor rbx, rax
	mov QWORD PTR [r9+32], rbx
	mov rbx, QWORD PTR [r9+120]
	xor rbx, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], rcx
	mov rcx, QWORD PTR [r9+64]
	xor rcx, QWORD PTR [r9+136]
	xor r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, QWORD PTR [r9+8]
	xor r10, rbp
	xor r12, rax
	xor r13, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+152]
	mov rax, QWORD PTR [r9+72]
	xor rax, QWORD PTR [r9+144]
	xor rbx, QWORD PTR [r9+128]
	xor r15, QWORD PTR [r9+96]
	xor r11, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rbx
	mov rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9+152]
	xor rbp, r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+16]
	mov QWORD PTR [r9+152], r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+32]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9]
	xor r10, QWORD PTR [r9+32]
	xor r10, QWORD PTR [r9]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rbx
	xor r12, QWORD PTR [r9]
	xor r14, r13
	xor r14, QWORD PTR [r9]
	xor r15, rbp
	xor r11, rcx
	xor r11, QWORD PTR [r9]
	mov r13, r15
	mov QWORD PTR [r9+80], r12
	mov r12, r11
	mov r11, rax
	mov QWORD PTR [r9+32], r10
	mov r10, QWORD PTR [r9+144]
	mov rbp, QWORD PTR [r9+80]
	mov rcx, QWORD PTR [r9+32]
	mov rbx, r14
	mov rax, QWORD PTR [r9+152]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+408]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+408]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+408]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+408]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+408]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+408]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+408]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+408]
	xor rax, r14
	mov r15, rax
	mov r14, rax
	xor r14, rbx
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov r14, rbx
	xor r14, rcx
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	mov r14, rcx
	xor r14, rbp
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	mov r14, rbp
	xor r14, r10
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	mov r14, r10
	xor r14, r11
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	mov r14, r11
	xor r14, r12
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	mov r14, r12
	xor r14, r13
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	mov r14, r13
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	xor r13, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	xor rax, QWORD PTR [r9+512]
	mov QWORD PTR [r9+512], rax
	xor rbx, QWORD PTR [r9+520]
	mov QWORD PTR [r9+520], rbx
	xor rcx, QWORD PTR [r9+528]
	mov QWORD PTR [r9+528], rcx
	xor rbp, QWORD PTR [r9+536]
	mov QWORD PTR [r9+536], rbp
	xor r10, QWORD PTR [r9+544]
	mov QWORD PTR [r9+544], r10
	xor r11, QWORD PTR [r9+552]
	mov QWORD PTR [r9+552], r11
	xor r12, QWORD PTR [r9+560]
	mov QWORD PTR [r9+560], r12
	xor r13, QWORD PTR [r9+568]
	mov QWORD PTR [r9+568], r13
	add rsi, 128
	cmp rsi, rdi
	jne 23b
	mov r14, QWORD PTR [r9+2944]
	cmp rsi, r14
	jne 24f
	jmp 25f
24:
	mov rax, QWORD PTR [r9+576]
	mov rbx, QWORD PTR [r9+584]
	mov rcx, QWORD PTR [r9+592]
	mov rbp, QWORD PTR [r9+600]
	mov r10, QWORD PTR [r9+608]
	mov r11, QWORD PTR [r9+616]
	mov r12, QWORD PTR [r9+624]
	mov r13, QWORD PTR [r9+632]
	mov r14, r13
	or r14, QWORD PTR [rsi+120]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r12
	or r14, QWORD PTR [rsi+112]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r11
	or r14, QWORD PTR [rsi+104]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r10
	or r14, QWORD PTR [rsi+96]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, rbp
	or r14, QWORD PTR [rsi+88]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rcx
	or r14, QWORD PTR [rsi+80]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbx
	or r14, QWORD PTR [rsi+72]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rax
	or r14, QWORD PTR [rsi+64]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r15, r13
	mov r14, r12
	and r14, QWORD PTR [rsi+112]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r11
	and r14, QWORD PTR [rsi+104]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r10
	and r14, QWORD PTR [rsi+96]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, rbp
	and r14, QWORD PTR [rsi+88]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, rcx
	and r14, QWORD PTR [rsi+80]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbx
	and r14, QWORD PTR [rsi+72]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rax
	and r14, QWORD PTR [rsi+64]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, r15
	and r14, QWORD PTR [rsi+120]
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov QWORD PTR [r9+576], rax
	mov QWORD PTR [r9+584], rbx
	mov QWORD PTR [r9+592], rcx
	mov QWORD PTR [r9+600], rbp
	mov QWORD PTR [r9+608], r10
	mov QWORD PTR [r9+616], r11
	mov QWORD PTR [r9+624], r12
	mov QWORD PTR [r9+632], r13
	mov rax, QWORD PTR [r9+512]
	mov rbx, QWORD PTR [r9+520]
	mov rcx, QWORD PTR [r9+528]
	mov rbp, QWORD PTR [r9+536]
	mov r10, QWORD PTR [r9+544]
	mov r11, QWORD PTR [r9+552]
	mov r12, QWORD PTR [r9+560]
	mov r13, QWORD PTR [r9+568]
	mov r15, r13
	mov r14, r12
	and r14, QWORD PTR [rsi+48]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r11
	and r14, QWORD PTR [rsi+40]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r10
	and r14, QWORD PTR [rsi+32]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, rbp
	and r14, QWORD PTR [rsi+24]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, rcx
	and r14, QWORD PTR [rsi+16]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbx
	and r14, QWORD PTR [rsi+8]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rax
	and r14, QWORD PTR [rsi]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, r15
	and r14, QWORD PTR [rsi+56]
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, r13
	or r14, QWORD PTR [rsi+56]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r12
	or r14, QWORD PTR [rsi+48]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r11
	or r14, QWORD PTR [rsi+40]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r10
	or r14, QWORD PTR [rsi+32]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, rbp
	or r14, QWORD PTR [rsi+24]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rcx
	or r14, QWORD PTR [rsi+16]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbx
	or r14, QWORD PTR [rsi+8]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rax
	or r14, QWORD PTR [rsi]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov QWORD PTR [r9+512], rax
	mov QWORD PTR [r9+520], rbx
	mov QWORD PTR [r9+528], rcx
	mov QWORD PTR [r9+536], rbp
	mov QWORD PTR [r9+544], r10
	mov QWORD PTR [r9+552], r11
	mov QWORD PTR [r9+560], r12
	mov QWORD PTR [r9+568], r13
	add rsi, 128
25:
	mov r14, QWORD PTR [r9+2944]
	cmp rsi, r14
	jne 22b
	xor rax, QWORD PTR [rsi+64]
	xor rbx, QWORD PTR [rsi+72]
	xor rcx, QWORD PTR [rsi+80]
	xor rbp, QWORD PTR [rsi+88]
	xor r10, QWORD PTR [rsi+96]
	xor r11, QWORD PTR [rsi+104]
	xor r12, QWORD PTR [rsi+112]
	xor r13, QWORD PTR [rsi+120]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rdx+8], rax
	mov QWORD PTR [rdx+24], rbx
	mov QWORD PTR [rdx+40], rcx
	mov QWORD PTR [rdx+56], rbp
	mov QWORD PTR [rdx+72], r10
	mov QWORD PTR [rdx+88], r11
	mov QWORD PTR [rdx+104], r12
	mov QWORD PTR [rdx+120], r13
	mov rax, QWORD PTR [r9+576]
	mov rbx, QWORD PTR [r9+584]
	mov rcx, QWORD PTR [r9+592]
	mov rbp, QWORD PTR [r9+600]
	mov r10, QWORD PTR [r9+608]
	mov r11, QWORD PTR [r9+616]
	mov r12, QWORD PTR [r9+624]
	mov r13, QWORD PTR [r9+632]
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+16], rbx
	mov QWORD PTR [rdx+32], rcx
	mov QWORD PTR [rdx+48], rbp
	mov QWORD PTR [rdx+64], r10
	mov QWORD PTR [rdx+80], r11
	mov QWORD PTR [rdx+96], r12
	mov QWORD PTR [rdx+112], r13
	mov rbx, QWORD PTR [r9+2968]
	mov rbp, QWORD PTR [r9+2976]
	mov r12, QWORD PTR [r9+2984]
	mov r13, QWORD PTR [r9+2992]
	mov r14, QWORD PTR [r9+3000]
	mov r15, QWORD PTR [r9+3008]
	ret
	.p2align 6
