// The functions of `src/internal/vg_rsa_private_checked_precomputed_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_checked_precomputed_adx:
	lea rsp, [rsp-3240]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
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
	add rdi, 168
	mov rsi, rcx
	mov r8, QWORD PTR [rsp+3248]
	mov r9, rcx
	mov rax, QWORD PTR [rsp+3360]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+3368]
	mov QWORD PTR [rsp+104], rax
	call {vg_rsa_private_crt_precomputed_adx}
	mov QWORD PTR [rsp+152], rax
	mov eax, 1
	mov QWORD PTR [rsp+160], rax
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+128]
	mov rdx, QWORD PTR [rsp+3360]
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 7
	shr rcx, 3
	add rcx, rcx
	mov r8, QWORD PTR [rsp+136]
	mov r9, QWORD PTR [rsp+144]
	mov rax, rsp
	add rax, 168
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3344]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3352]
	mov QWORD PTR [rsp+24], rax
	call {vg_rsa_public_precomputed_checked_adx}
	and rax, QWORD PTR [rsp+152]
	and rax, QWORD PTR [rsp+160]
	and rax, 1
	mov r11, rax
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+3248]
	mov rcx, QWORD PTR [rsp+128]
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
	movzx eax, BYTE PTR [rsp+r10*1+168]
	and rax, r9
	mov BYTE PTR [rdi+r10*1], al
	mov eax, 0
	mov BYTE PTR [rsp+r10*1+168], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rax, r11
	lea rsp, [rsp+3240]
	ret
	.p2align 6
