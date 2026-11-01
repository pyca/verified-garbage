// The functions of `src/internal/vg_p521_mul_mod_n.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul_mod_n:
	mov esi, esi
	mov edx, edx
	mov ecx, ecx
	movq xmm0, rbx
	movq xmm1, rbp
	movq xmm2, r12
	movq xmm3, r13
	movq xmm4, r14
	movq xmm5, r15
	mov rbx, rdx
	add rbx, rdi
	add rcx, rdi
	cmp rbx, rcx
	mov rbp, rcx
	add rsi, rdi
	mov rax, QWORD PTR [rdi+3952]
	movq xmm6, rax
	mov rax, QWORD PTR [rdi+3960]
	movq xmm7, rax
	mov rax, QWORD PTR [rdi+3968]
	movq xmm8, rax
	mov rax, QWORD PTR [rdi+3976]
	movq xmm9, rax
	mov rax, QWORD PTR [rdi+3984]
	movq xmm10, rax
	mov rax, QWORD PTR [rdi+3992]
	movq xmm11, rax
	mov rax, QWORD PTR [rdi+4000]
	movq xmm12, rax
	mov rax, QWORD PTR [rdi+4008]
	movq xmm13, rax
	mov rax, QWORD PTR [rdi+4016]
	movq xmm14, rax
	movabs rax, -4940528924288850935
	mov QWORD PTR [rdi+3952], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+3960], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+3968], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+3976], rax
	movabs rax, -6
	mov QWORD PTR [rdi+3984], rax
	movabs rax, -1
	mov QWORD PTR [rdi+3992], rax
	movabs rax, -1
	mov QWORD PTR [rdi+4000], rax
	movabs rax, -1
	mov QWORD PTR [rdi+4008], rax
	movabs rax, 511
	mov QWORD PTR [rdi+4016], rax
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rbp]
	mov rax, QWORD PTR [rbx]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4024], rcx
	mov rax, QWORD PTR [rdi+3952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+8]
	mov rax, QWORD PTR [rbx]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp]
	mov rax, QWORD PTR [rbx+8]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3960]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4032], rcx
	mov rax, QWORD PTR [rdi+3952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+16]
	mov rax, QWORD PTR [rbx]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+8]
	mov rax, QWORD PTR [rbx+8]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp]
	mov rax, QWORD PTR [rbx+16]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3968]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3960]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4040], rcx
	mov rax, QWORD PTR [rdi+3952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+24]
	mov rax, QWORD PTR [rbx]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+16]
	mov rax, QWORD PTR [rbx+8]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+8]
	mov rax, QWORD PTR [rbx+16]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp]
	mov rax, QWORD PTR [rbx+24]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3976]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3968]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3960]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4048], rcx
	mov rax, QWORD PTR [rdi+3952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+32]
	mov rax, QWORD PTR [rbx]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+24]
	mov rax, QWORD PTR [rbx+8]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+16]
	mov rax, QWORD PTR [rbx+16]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+8]
	mov rax, QWORD PTR [rbx+24]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp]
	mov rax, QWORD PTR [rbx+32]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3984]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3976]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3968]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3960]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4056], rcx
	mov rax, QWORD PTR [rdi+3952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+40]
	mov rax, QWORD PTR [rbx]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+32]
	mov rax, QWORD PTR [rbx+8]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+24]
	mov rax, QWORD PTR [rbx+16]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+16]
	mov rax, QWORD PTR [rbx+24]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+8]
	mov rax, QWORD PTR [rbx+32]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp]
	mov rax, QWORD PTR [rbx+40]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3992]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3984]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3976]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3968]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3960]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4064], rcx
	mov rax, QWORD PTR [rdi+3952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+48]
	mov rax, QWORD PTR [rbx]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+40]
	mov rax, QWORD PTR [rbx+8]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+32]
	mov rax, QWORD PTR [rbx+16]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+24]
	mov rax, QWORD PTR [rbx+24]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+16]
	mov rax, QWORD PTR [rbx+32]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+8]
	mov rax, QWORD PTR [rbx+40]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp]
	mov rax, QWORD PTR [rbx+48]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4000]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3992]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3984]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3976]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3968]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3960]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4072], rcx
	mov rax, QWORD PTR [rdi+3952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+56]
	mov rax, QWORD PTR [rbx]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+48]
	mov rax, QWORD PTR [rbx+8]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+40]
	mov rax, QWORD PTR [rbx+16]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+32]
	mov rax, QWORD PTR [rbx+24]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+24]
	mov rax, QWORD PTR [rbx+32]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+16]
	mov rax, QWORD PTR [rbx+40]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+8]
	mov rax, QWORD PTR [rbx+48]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp]
	mov rax, QWORD PTR [rbx+56]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4008]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4000]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3992]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3984]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3976]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3968]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3960]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4080], rcx
	mov rax, QWORD PTR [rdi+3952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+64]
	mov rax, QWORD PTR [rbx]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+56]
	mov rax, QWORD PTR [rbx+8]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+48]
	mov rax, QWORD PTR [rbx+16]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+40]
	mov rax, QWORD PTR [rbx+24]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+32]
	mov rax, QWORD PTR [rbx+32]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+24]
	mov rax, QWORD PTR [rbx+40]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+16]
	mov rax, QWORD PTR [rbx+48]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+8]
	mov rax, QWORD PTR [rbx+56]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp]
	mov rax, QWORD PTR [rbx+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4016]
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4008]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4000]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3992]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3984]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3976]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3968]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3960]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, 2103001588584519111
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+4088], rcx
	mov rax, QWORD PTR [rdi+3952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+64]
	mov rax, QWORD PTR [rbx+8]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+56]
	mov rax, QWORD PTR [rbx+16]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+48]
	mov rax, QWORD PTR [rbx+24]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+40]
	mov rax, QWORD PTR [rbx+32]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+32]
	mov rax, QWORD PTR [rbx+40]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+24]
	mov rax, QWORD PTR [rbx+48]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+16]
	mov rax, QWORD PTR [rbx+56]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+8]
	mov rax, QWORD PTR [rbx+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4016]
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4008]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4000]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3992]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3984]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3976]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3968]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3960]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rbp+64]
	mov rax, QWORD PTR [rbx+16]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+56]
	mov rax, QWORD PTR [rbx+24]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+48]
	mov rax, QWORD PTR [rbx+32]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+40]
	mov rax, QWORD PTR [rbx+40]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+32]
	mov rax, QWORD PTR [rbx+48]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+24]
	mov rax, QWORD PTR [rbx+56]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+16]
	mov rax, QWORD PTR [rbx+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4016]
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4008]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4000]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3992]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3984]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3976]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3968]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rbp+64]
	mov rax, QWORD PTR [rbx+24]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+56]
	mov rax, QWORD PTR [rbx+32]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+48]
	mov rax, QWORD PTR [rbx+40]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+40]
	mov rax, QWORD PTR [rbx+48]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+32]
	mov rax, QWORD PTR [rbx+56]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+24]
	mov rax, QWORD PTR [rbx+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4016]
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4008]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4000]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3992]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3984]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+3976]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rbp+64]
	mov rax, QWORD PTR [rbx+32]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+56]
	mov rax, QWORD PTR [rbx+40]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+48]
	mov rax, QWORD PTR [rbx+48]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+40]
	mov rax, QWORD PTR [rbx+56]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+32]
	mov rax, QWORD PTR [rbx+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4016]
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4008]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4000]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3992]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+3984]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rbp+64]
	mov rax, QWORD PTR [rbx+40]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+56]
	mov rax, QWORD PTR [rbx+48]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+48]
	mov rax, QWORD PTR [rbx+56]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rbp+40]
	mov rax, QWORD PTR [rbx+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4016]
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4008]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4000]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+3992]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rbp+64]
	mov rax, QWORD PTR [rbx+48]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+56]
	mov rax, QWORD PTR [rbx+56]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rbp+48]
	mov rax, QWORD PTR [rbx+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4016]
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4008]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+4000]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rbp+64]
	mov rax, QWORD PTR [rbx+56]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rbp+56]
	mov rax, QWORD PTR [rbx+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4016]
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+4008]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rbp+64]
	mov rax, QWORD PTR [rbx+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+4016]
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+3952]
	mov QWORD PTR [rsi], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+3960]
	mov QWORD PTR [rsi+8], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+3968]
	mov QWORD PTR [rsi+16], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+3976]
	mov QWORD PTR [rsi+24], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+3984]
	mov QWORD PTR [rsi+32], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+3992]
	mov QWORD PTR [rsi+40], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+4000]
	mov QWORD PTR [rsi+48], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+4008]
	mov QWORD PTR [rsi+56], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+4016]
	mov QWORD PTR [rsi+64], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rsi]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rsi], rdx
	mov rdx, QWORD PTR [rsi+8]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rsi+8], rdx
	mov rdx, QWORD PTR [rsi+16]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rsi+16], rdx
	mov rdx, QWORD PTR [rsi+24]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rsi+24], rdx
	mov rdx, QWORD PTR [rsi+32]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rsi+32], rdx
	mov rdx, QWORD PTR [rsi+40]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rsi+40], rdx
	mov rdx, QWORD PTR [rsi+48]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rsi+48], rdx
	mov rdx, QWORD PTR [rsi+56]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rsi+56], rdx
	mov rdx, QWORD PTR [rsi+64]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rsi+64], rdx
	movq rax, xmm6
	mov QWORD PTR [rdi+3952], rax
	movq rax, xmm7
	mov QWORD PTR [rdi+3960], rax
	movq rax, xmm8
	mov QWORD PTR [rdi+3968], rax
	movq rax, xmm9
	mov QWORD PTR [rdi+3976], rax
	movq rax, xmm10
	mov QWORD PTR [rdi+3984], rax
	movq rax, xmm11
	mov QWORD PTR [rdi+3992], rax
	movq rax, xmm12
	mov QWORD PTR [rdi+4000], rax
	movq rax, xmm13
	mov QWORD PTR [rdi+4008], rax
	movq rax, xmm14
	mov QWORD PTR [rdi+4016], rax
	movq rbx, xmm0
	movq rbp, xmm1
	movq r12, xmm2
	movq r13, xmm3
	movq r14, xmm4
	movq r15, xmm5
	ret
	.p2align 6
