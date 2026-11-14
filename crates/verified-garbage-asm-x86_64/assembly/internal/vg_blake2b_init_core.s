// The functions of `src/internal/vg_blake2b_init_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init_core:
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	movabs rax, 7640891576939301128
	mov r8, rcx
	ror r8, 56
	xor rax, r8
	xor rax, rsi
	mov QWORD PTR [rdi], rax
	test rcx, rcx
	je 20f
	mov eax, 0
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov r8d, 0
22:
	movzx eax, BYTE PTR [rdx+r8*1]
	mov BYTE PTR [rdi+r8*1+64], al
	add r8, 1
	sub rcx, 1
	jne 22b
	jmp 21f
20:
21:
	ret
	.p2align 6
