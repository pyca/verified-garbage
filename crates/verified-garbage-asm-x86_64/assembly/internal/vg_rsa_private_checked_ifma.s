// The functions of `src/internal/vg_rsa_private_checked_ifma.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_checked_ifma:
	lea rsp, [rsp-3240]
	mov QWORD PTR [rsp+96], rdi
	mov QWORD PTR [rsp+104], rdx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], r8
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+3264]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+3272]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3280]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3288]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+3296]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+3304]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+3312]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+3320]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+3328]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+3336]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+3344]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+3352]
	mov QWORD PTR [rsp+88], rax
	mov rdi, rsp
	add rdi, 160
	mov rsi, rcx
	mov r8, QWORD PTR [rsp+3248]
	mov r9, rcx
	call {vg_rsa_private_crt_ifma}
	mov QWORD PTR [rsp+136], rax
	mov rdi, rsp
	add rdi, 1184
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 7
	shr rsi, 3
	add rsi, rsi
	mov rdx, QWORD PTR [rsp+104]
	mov rcx, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+3344]
	mov r9, QWORD PTR [rsp+3352]
	call {vg_rsa_public_precompute_adx}
	mov QWORD PTR [rsp+144], rax
	mov rdi, QWORD PTR [rsp+96]
	mov rsi, QWORD PTR [rsp+112]
	mov rdx, rsp
	add rdx, 1184
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 7
	shr rcx, 3
	add rcx, rcx
	mov r8, QWORD PTR [rsp+120]
	mov r9, QWORD PTR [rsp+128]
	mov rax, rsp
	add rax, 160
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3344]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3352]
	mov QWORD PTR [rsp+24], rax
	call {vg_rsa_public_precomputed_checked_ifma}
	and rax, QWORD PTR [rsp+136]
	and rax, QWORD PTR [rsp+144]
	and rax, 1
	mov r11, rax
	mov rdi, QWORD PTR [rsp+96]
	mov rsi, QWORD PTR [rsp+3248]
	mov rcx, QWORD PTR [rsp+112]
	mov r10d, 0
	mov edx, 0
20:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r9d, BYTE PTR [rsi+r10*1]
	xor rax, r9
	or rdx, rax
	add r10, 1
	cmp r10, rcx
	jne 20b
	cmp rdx, 1
	sbb rdx, rdx
	mov r9d, 0
	sub r9, r11
	mov rax, rdx
	and rax, 1
	mov r8d, 2
	sub r8, rax
	and r8, r9
	and r9, rdx
	mov r11, r8
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsp+r10*1+160]
	and rax, r9
	mov BYTE PTR [rdi+r10*1], al
	mov eax, 0
	mov BYTE PTR [rsp+r10*1+160], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rax, r11
	lea rsp, [rsp+3240]
	ret
	.p2align 6
