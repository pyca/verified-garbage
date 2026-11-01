// The functions of `src/internal/vg_p384_check_point.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_check_point:
	movq xmm0, rbx
	movq xmm1, rbp
	movq xmm2, r12
	movq xmm3, r13
	movq xmm4, r14
	movq xmm5, r15
	mov rdx, QWORD PTR [rdi+1648]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+1656]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+1664]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+1672]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+1680]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1688]
	sbb rdx, QWORD PTR [rdi+104]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1792]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+1800]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+1808]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+1816]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+1824]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1832]
	sbb rdx, QWORD PTR [rdi+104]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1696], r14
	mov QWORD PTR [rdi+1704], r15
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1744], r14
	mov QWORD PTR [rdi+1752], r15
	mov QWORD PTR [rdi+1760], r8
	mov QWORD PTR [rdi+1768], r9
	mov QWORD PTR [rdi+1776], r10
	mov QWORD PTR [rdi+1784], r11
	mov rcx, QWORD PTR [rdi+1744]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1744]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1752]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1760]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1768]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1776]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1784]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	mov QWORD PTR [rdi+1864], r8
	mov QWORD PTR [rdi+1872], r9
	mov QWORD PTR [rdi+1880], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1840]
	adc r14, QWORD PTR [rdi+1848]
	adc r15, QWORD PTR [rdi+1856]
	adc r10, QWORD PTR [rdi+1864]
	adc r11, QWORD PTR [rdi+1872]
	adc r12, QWORD PTR [rdi+1880]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1840], r13
	mov QWORD PTR [rdi+1848], r14
	mov QWORD PTR [rdi+1856], r15
	mov QWORD PTR [rdi+1864], r10
	mov QWORD PTR [rdi+1872], r11
	mov QWORD PTR [rdi+1880], r12
	mov rcx, QWORD PTR [rdi+1696]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1704]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1712]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1720]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1728]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1696]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1704]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1712]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1720]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1728]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1736]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+2032], r13
	mov QWORD PTR [rdi+2040], r14
	mov QWORD PTR [rdi+2048], r15
	mov QWORD PTR [rdi+2056], r8
	mov QWORD PTR [rdi+2064], r9
	mov QWORD PTR [rdi+2072], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+2032]
	adc r14, QWORD PTR [rdi+2040]
	adc r15, QWORD PTR [rdi+2048]
	adc r10, QWORD PTR [rdi+2056]
	adc r11, QWORD PTR [rdi+2064]
	adc r12, QWORD PTR [rdi+2072]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+2032], r13
	mov QWORD PTR [rdi+2040], r14
	mov QWORD PTR [rdi+2048], r15
	mov QWORD PTR [rdi+2056], r10
	mov QWORD PTR [rdi+2064], r11
	mov QWORD PTR [rdi+2072], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2064]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+2072]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+2080], r14
	mov QWORD PTR [rdi+2088], r15
	mov QWORD PTR [rdi+2096], r8
	mov QWORD PTR [rdi+2104], r9
	mov QWORD PTR [rdi+2112], r10
	mov QWORD PTR [rdi+2120], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+2032], r14
	mov QWORD PTR [rdi+2040], r15
	mov QWORD PTR [rdi+2048], r8
	mov QWORD PTR [rdi+2056], r9
	mov QWORD PTR [rdi+2064], r10
	mov QWORD PTR [rdi+2072], r11
	mov r8, QWORD PTR [rdi+2080]
	mov r9, QWORD PTR [rdi+2088]
	mov r10, QWORD PTR [rdi+2096]
	mov r11, QWORD PTR [rdi+2104]
	mov r12, QWORD PTR [rdi+2112]
	mov r13, QWORD PTR [rdi+2120]
	mov r14d, 0
	add r8, QWORD PTR [rdi+2032]
	adc r9, QWORD PTR [rdi+2040]
	adc r10, QWORD PTR [rdi+2048]
	adc r11, QWORD PTR [rdi+2056]
	adc r12, QWORD PTR [rdi+2064]
	adc r13, QWORD PTR [rdi+2072]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1888], r8
	mov QWORD PTR [rdi+1896], r9
	mov QWORD PTR [rdi+1904], r10
	mov QWORD PTR [rdi+1912], r11
	mov QWORD PTR [rdi+1920], r12
	mov QWORD PTR [rdi+1928], r13
	mov r8, QWORD PTR [rdi+1888]
	mov r9, QWORD PTR [rdi+1896]
	mov r10, QWORD PTR [rdi+1904]
	mov r11, QWORD PTR [rdi+1912]
	mov r12, QWORD PTR [rdi+1920]
	mov r13, QWORD PTR [rdi+1928]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1984]
	adc r9, QWORD PTR [rdi+1992]
	adc r10, QWORD PTR [rdi+2000]
	adc r11, QWORD PTR [rdi+2008]
	adc r12, QWORD PTR [rdi+2016]
	adc r13, QWORD PTR [rdi+2024]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+2080], r8
	mov QWORD PTR [rdi+2088], r9
	mov QWORD PTR [rdi+2096], r10
	mov QWORD PTR [rdi+2104], r11
	mov QWORD PTR [rdi+2112], r12
	mov QWORD PTR [rdi+2120], r13
	mov r8, QWORD PTR [rdi+1840]
	mov r9, QWORD PTR [rdi+1848]
	mov r10, QWORD PTR [rdi+1856]
	mov r11, QWORD PTR [rdi+1864]
	mov r12, QWORD PTR [rdi+1872]
	mov r13, QWORD PTR [rdi+1880]
	sub r8, QWORD PTR [rdi+2080]
	sbb r9, QWORD PTR [rdi+2088]
	sbb r10, QWORD PTR [rdi+2096]
	sbb r11, QWORD PTR [rdi+2104]
	sbb r12, QWORD PTR [rdi+2112]
	sbb r13, QWORD PTR [rdi+2120]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+2032], r8
	mov QWORD PTR [rdi+2040], r9
	mov QWORD PTR [rdi+2048], r10
	mov QWORD PTR [rdi+2056], r11
	mov QWORD PTR [rdi+2064], r12
	mov QWORD PTR [rdi+2072], r13
	mov rdx, QWORD PTR [rdi+2032]
	or rdx, QWORD PTR [rdi+2040]
	or rdx, QWORD PTR [rdi+2048]
	or rdx, QWORD PTR [rdi+2056]
	or rdx, QWORD PTR [rdi+2064]
	or rdx, QWORD PTR [rdi+2072]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+448]
	mov rdx, QWORD PTR [rdi+1696]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1888], rax
	mov rax, QWORD PTR [rdi+456]
	mov rdx, QWORD PTR [rdi+1704]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1896], rax
	mov rax, QWORD PTR [rdi+464]
	mov rdx, QWORD PTR [rdi+1712]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1904], rax
	mov rax, QWORD PTR [rdi+472]
	mov rdx, QWORD PTR [rdi+1720]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1912], rax
	mov rax, QWORD PTR [rdi+480]
	mov rdx, QWORD PTR [rdi+1728]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1920], rax
	mov rax, QWORD PTR [rdi+488]
	mov rdx, QWORD PTR [rdi+1736]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1928], rax
	mov rax, QWORD PTR [rdi+496]
	mov rdx, QWORD PTR [rdi+1744]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2128], rax
	mov rax, QWORD PTR [rdi+504]
	mov rdx, QWORD PTR [rdi+1752]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2136], rax
	mov rax, QWORD PTR [rdi+512]
	mov rdx, QWORD PTR [rdi+1760]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2144], rax
	mov rax, QWORD PTR [rdi+520]
	mov rdx, QWORD PTR [rdi+1768]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2152], rax
	mov rax, QWORD PTR [rdi+528]
	mov rdx, QWORD PTR [rdi+1776]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2160], rax
	mov rax, QWORD PTR [rdi+536]
	mov rdx, QWORD PTR [rdi+1784]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2168], rax
	movq rbx, xmm0
	movq rbp, xmm1
	movq r12, xmm2
	movq r13, xmm3
	movq r14, xmm4
	movq r15, xmm5
	ret
	.p2align 6
