// The functions of `src/internal/vg_blake2b_compress.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_compress:
	mov QWORD PTR [r9+296], rbx
	mov QWORD PTR [r9+304], rbp
	mov QWORD PTR [r9+312], r12
	mov QWORD PTR [r9+320], r13
	mov QWORD PTR [r9+328], r14
	mov QWORD PTR [r9+336], r15
	mov r8d, r8d
	mov QWORD PTR [r9+256], rsi
	mov QWORD PTR [r9+264], rdx
	mov QWORD PTR [r9+272], rcx
	mov eax, 0
	mov QWORD PTR [r9+280], rax
	test r8, r8
	je 20f
	mov rax, -1
	jmp 21f
20:
21:
	mov QWORD PTR [r9+288], rax
	test rdx, rdx
	je 22f
24:
	mov rsi, QWORD PTR [r9+256]
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [r9], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [r9+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [r9+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [r9+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [r9+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [r9+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [r9+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [r9+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [r9+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [r9+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [r9+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [r9+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [r9+120], rax
	movabs rax, 7640891576956012808
	mov QWORD PTR [r9+192], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [r9+200], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [r9+208], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [r9+216], rax
	mov rax, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rcx, QWORD PTR [rdi+16]
	mov rdx, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	mov rbp, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+56]
	movabs r10, 5840696475078001361
	xor r10, QWORD PTR [r9+272]
	movabs r11, -7276294671716946913
	xor r11, QWORD PTR [r9+280]
	movabs r12, 2270897969802886507
	xor r12, QWORD PTR [r9+288]
	movabs r13, 6620516959819538809
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+16]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+32]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+48]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+8]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+24]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+40]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+56]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+64]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+80]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+96]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+112]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+72]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+88]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+104]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+120]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+112]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+32]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+72]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+104]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+80]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+64]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+120]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+48]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+8]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+88]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+40]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+96]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+16]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+56]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+24]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+88]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+96]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+40]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+120]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+64]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+16]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+104]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+80]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+24]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+56]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+72]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+112]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+48]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+8]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+32]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+56]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+24]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+104]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+88]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+72]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+8]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+96]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+112]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+16]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+40]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+32]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+120]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+48]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+80]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+64]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+72]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+40]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+16]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+80]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+56]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+32]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+120]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+112]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+88]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+48]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+24]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+8]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+96]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+64]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+104]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+16]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+48]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+64]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+96]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+80]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+88]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+24]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+32]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+56]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+120]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+8]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+104]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+40]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+112]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+72]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+96]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+8]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+112]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+32]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+40]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+120]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+104]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+80]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+48]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+72]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+64]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+56]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+24]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+16]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+88]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+104]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+56]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+96]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+24]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+88]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+112]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+8]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+72]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+40]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+120]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+64]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+16]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+32]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+48]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+80]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+48]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+112]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+88]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+120]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+72]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+24]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+64]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+96]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+104]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+8]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+80]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+16]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+56]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+32]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+40]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+80]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+64]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+56]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+8]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+16]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+32]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+48]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+40]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+120]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+72]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+24]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+104]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+88]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+112]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+96]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+16]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+32]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+48]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+8]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+24]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+40]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+56]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+64]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+80]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+96]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+112]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+72]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+88]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+104]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+120]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+112]
	add rax, r14
	xor r10, rax
	ror r10, 32
	add rsi, r10
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+32]
	add rbx, r15
	xor r11, rbx
	ror r11, 32
	add rsi, r11
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+72]
	add rcx, rbp
	xor r12, rcx
	ror r12, 32
	add rsi, r12
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+104]
	add rdx, r8
	xor r13, rdx
	ror r13, 32
	add rsi, r13
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rax, QWORD PTR [r9+80]
	add rax, r14
	xor r10, rax
	ror r10, 16
	add rsi, r10
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rbx, QWORD PTR [r9+64]
	add rbx, r15
	xor r11, rbx
	ror r11, 16
	add rsi, r11
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rcx, QWORD PTR [r9+120]
	add rcx, rbp
	xor r12, rcx
	ror r12, 16
	add rsi, r12
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rdx, QWORD PTR [r9+48]
	add rdx, r8
	xor r13, rdx
	ror r13, 16
	add rsi, r13
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+8]
	add rax, r15
	xor r13, rax
	ror r13, 32
	add rsi, r13
	xor r15, rsi
	ror r15, 24
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9]
	add rbx, rbp
	xor r10, rbx
	ror r10, 32
	add rsi, r10
	xor rbp, rsi
	ror rbp, 24
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+88]
	add rcx, r8
	xor r11, rcx
	ror r11, 32
	add rsi, r11
	xor r8, rsi
	ror r8, 24
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+40]
	add rdx, r14
	xor r12, rdx
	ror r12, 32
	add rsi, r12
	xor r14, rsi
	ror r14, 24
	mov QWORD PTR [r9+200], rsi
	mov rsi, QWORD PTR [r9+208]
	add rax, QWORD PTR [r9+96]
	add rax, r15
	xor r13, rax
	ror r13, 16
	add rsi, r13
	xor r15, rsi
	ror r15, 63
	mov QWORD PTR [r9+208], rsi
	mov rsi, QWORD PTR [r9+216]
	add rbx, QWORD PTR [r9+16]
	add rbx, rbp
	xor r10, rbx
	ror r10, 16
	add rsi, r10
	xor rbp, rsi
	ror rbp, 63
	mov QWORD PTR [r9+216], rsi
	mov rsi, QWORD PTR [r9+192]
	add rcx, QWORD PTR [r9+56]
	add rcx, r8
	xor r11, rcx
	ror r11, 16
	add rsi, r11
	xor r8, rsi
	ror r8, 63
	mov QWORD PTR [r9+192], rsi
	mov rsi, QWORD PTR [r9+200]
	add rdx, QWORD PTR [r9+24]
	add rdx, r14
	xor r12, rdx
	ror r12, 16
	add rsi, r12
	xor r14, rsi
	ror r14, 63
	mov QWORD PTR [r9+200], rsi
	mov QWORD PTR [r9+224], r10
	mov QWORD PTR [r9+232], r11
	mov QWORD PTR [r9+240], r12
	mov QWORD PTR [r9+248], r13
	xor rax, QWORD PTR [r9+192]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	xor rbx, QWORD PTR [r9+200]
	xor rbx, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rbx
	xor rcx, QWORD PTR [r9+208]
	xor rcx, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rcx
	xor rdx, QWORD PTR [r9+216]
	xor rdx, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rdx
	xor r14, QWORD PTR [r9+224]
	xor r14, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], r14
	xor r15, QWORD PTR [r9+232]
	xor r15, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], r15
	xor rbp, QWORD PTR [r9+240]
	xor rbp, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rbp
	xor r8, QWORD PTR [r9+248]
	xor r8, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], r8
	mov rsi, QWORD PTR [r9+256]
	add rsi, 128
	mov QWORD PTR [r9+256], rsi
	mov rcx, QWORD PTR [r9+272]
	add rcx, 128
	mov QWORD PTR [r9+272], rcx
	mov r8, QWORD PTR [r9+280]
	adc r8, 0
	mov QWORD PTR [r9+280], r8
	mov rdx, QWORD PTR [r9+264]
	sub rdx, 1
	mov QWORD PTR [r9+264], rdx
	jne 24b
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+296]
	mov rbp, QWORD PTR [r9+304]
	mov r12, QWORD PTR [r9+312]
	mov r13, QWORD PTR [r9+320]
	mov r14, QWORD PTR [r9+328]
	mov r15, QWORD PTR [r9+336]
	ret
	.p2align 6
