// The functions of `src/idea_cfb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_idea_cfb64_encrypt:
	lea rsp, [rsp-184]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+112], rbx
	mov QWORD PTR [r9+120], rbp
	mov QWORD PTR [r9+128], r12
	mov QWORD PTR [r9+136], r13
	mov QWORD PTR [r9+144], r14
	mov QWORD PTR [r9+152], r15
	movq xmm15, rsi
	mov r12, rdx
	mov r13, rcx
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+8], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+16], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+24], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+32], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [r9+40], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [r9+48], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [r9+56], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r9+72], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [r9+88], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [r9+96], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [r9+104], rax
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9], rbp
	test r13, r13
	je 20f
22:
	mov rcx, r9
	mov rdi, r9
	add rdi, 8
	mov rsi, r9
	movzx r8d, BYTE PTR [rsi]
	shl r8, 8
	movzx eax, BYTE PTR [rsi+1]
	or r8, rax
	movzx r9d, BYTE PTR [rsi+2]
	shl r9, 8
	movzx eax, BYTE PTR [rsi+3]
	or r9, rax
	movzx r10d, BYTE PTR [rsi+4]
	shl r10, 8
	movzx eax, BYTE PTR [rsi+5]
	or r10, rax
	movzx r11d, BYTE PTR [rsi+6]
	shl r11, 8
	movzx eax, BYTE PTR [rsi+7]
	or r11, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+6]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+2]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+4]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+8]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+10]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+12]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+18]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+14]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+16]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+20]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+22]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+24]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+30]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+26]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+28]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+32]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+34]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+36]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+42]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+38]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+40]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+44]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+46]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+48]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+54]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+50]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+52]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+56]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+58]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+60]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+66]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+62]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+64]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+68]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+70]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+72]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+78]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+74]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+76]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+80]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+82]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+84]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+90]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+86]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+88]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+92]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+94]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+96]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+96]
	shr rdx, 48
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+96]
	shr rdx, 16
	add r10, rdx
	and r10, 65535
	mov rdx, QWORD PTR [rdi+96]
	shr rdx, 32
	add r9, rdx
	and r9, 65535
	mov BYTE PTR [rsi+1], r8b
	mov rax, r8
	shr rax, 8
	mov BYTE PTR [rsi], al
	mov BYTE PTR [rsi+3], r10b
	mov rax, r10
	shr rax, 8
	mov BYTE PTR [rsi+2], al
	mov BYTE PTR [rsi+5], r9b
	mov rax, r9
	shr rax, 8
	mov BYTE PTR [rsi+4], al
	mov BYTE PTR [rsi+7], r11b
	mov rax, r11
	shr rax, 8
	mov BYTE PTR [rsi+6], al
	mov r9, rcx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r9], rax
	add r12, 8
	sub r13, 1
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9]
	mov QWORD PTR [rax], rbp
	mov rbx, QWORD PTR [r9+112]
	mov rbp, QWORD PTR [r9+120]
	mov r12, QWORD PTR [r9+128]
	mov r13, QWORD PTR [r9+136]
	mov r14, QWORD PTR [r9+144]
	mov r15, QWORD PTR [r9+152]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	lea rsp, [rsp+184]
	ret
	.p2align 6

vg_idea_cfb64_decrypt:
	lea rsp, [rsp-184]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+112], rbx
	mov QWORD PTR [r9+120], rbp
	mov QWORD PTR [r9+128], r12
	mov QWORD PTR [r9+136], r13
	mov QWORD PTR [r9+144], r14
	mov QWORD PTR [r9+152], r15
	movq xmm15, rsi
	mov r12, rdx
	mov r13, rcx
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+8], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+16], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+24], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+32], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [r9+40], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [r9+48], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [r9+56], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r9+72], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [r9+88], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [r9+96], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [r9+104], rax
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9], rbp
	test r13, r13
	je 20f
22:
	mov rcx, r9
	mov rdi, r9
	add rdi, 8
	mov rsi, r9
	movzx r8d, BYTE PTR [rsi]
	shl r8, 8
	movzx eax, BYTE PTR [rsi+1]
	or r8, rax
	movzx r9d, BYTE PTR [rsi+2]
	shl r9, 8
	movzx eax, BYTE PTR [rsi+3]
	or r9, rax
	movzx r10d, BYTE PTR [rsi+4]
	shl r10, 8
	movzx eax, BYTE PTR [rsi+5]
	or r10, rax
	movzx r11d, BYTE PTR [rsi+6]
	shl r11, 8
	movzx eax, BYTE PTR [rsi+7]
	or r11, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+6]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+2]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+4]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+8]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+10]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+12]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+18]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+14]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+16]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+20]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+22]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+24]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+30]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+26]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+28]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+32]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+34]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+36]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+42]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+38]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+40]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+44]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+46]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+48]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+54]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+50]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+52]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+56]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+58]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+60]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+66]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+62]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+64]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+68]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+70]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+72]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+78]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+74]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+76]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+80]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+82]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+84]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+90]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+86]
	add r9, rdx
	and r9, 65535
	mov rdx, QWORD PTR [rdi+88]
	add r10, rdx
	and r10, 65535
	mov rax, r8
	xor rax, r10
	mov rdx, QWORD PTR [rdi+92]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov rbx, rdx
	mov rax, r9
	xor rax, r11
	add rax, rbx
	mov rdx, QWORD PTR [rdi+94]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	add rbx, rdx
	and rbx, 65535
	xor r8, rdx
	xor r10, rdx
	xor r9, rbx
	xor r11, rbx
	mov rax, r9
	mov r9, r10
	mov r10, rax
	mov rax, r8
	mov rdx, QWORD PTR [rdi+96]
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r8, rdx
	mov rax, r11
	mov rdx, QWORD PTR [rdi+96]
	shr rdx, 48
	sub rax, 1
	and rax, 65535
	add rax, 1
	sub rdx, 1
	and rdx, 65535
	add rdx, 1
	imul rax, rdx
	mov rdx, rax
	and rdx, 65535
	shr rax, 16
	sub rdx, rax
	mov rax, rdx
	shr rax, 63
	add rdx, rax
	shl rax, 16
	add rdx, rax
	and rdx, 65535
	mov r11, rdx
	mov rdx, QWORD PTR [rdi+96]
	shr rdx, 16
	add r10, rdx
	and r10, 65535
	mov rdx, QWORD PTR [rdi+96]
	shr rdx, 32
	add r9, rdx
	and r9, 65535
	mov BYTE PTR [rsi+1], r8b
	mov rax, r8
	shr rax, 8
	mov BYTE PTR [rsi], al
	mov BYTE PTR [rsi+3], r10b
	mov rax, r10
	shr rax, 8
	mov BYTE PTR [rsi+2], al
	mov BYTE PTR [rsi+5], r9b
	mov rax, r9
	shr rax, 8
	mov BYTE PTR [rsi+4], al
	mov BYTE PTR [rsi+7], r11b
	mov rax, r11
	shr rax, 8
	mov BYTE PTR [rsi+6], al
	mov r9, rcx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r9]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [r9], rax
	add r12, 8
	sub r13, 1
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9]
	mov QWORD PTR [rax], rbp
	mov rbx, QWORD PTR [r9+112]
	mov rbp, QWORD PTR [r9+120]
	mov r12, QWORD PTR [r9+128]
	mov r13, QWORD PTR [r9+136]
	mov r14, QWORD PTR [r9+144]
	mov r15, QWORD PTR [r9+152]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	lea rsp, [rsp+184]
	ret
	.p2align 6
