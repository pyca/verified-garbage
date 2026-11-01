// The functions of `src/blake2b.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init:
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

vg_blake2b_update_avx2:
	lea rsp, [rsp-584]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+512], rbx
	mov QWORD PTR [r8+520], rbp
	mov QWORD PTR [r8+528], r12
	mov QWORD PTR [r8+536], r13
	mov QWORD PTR [r8+544], r14
	mov QWORD PTR [r8+552], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 127
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	test r12, r12
	je 22f
	test r13, r13
	je 24f
	mov eax, 128
	sub rax, r13
	cmp r12, rax
	jb 26f
	jmp 27f
26:
	mov rax, r12
27:
	sub r12, rax
	add r14, rax
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	test r12, r12
	je 211f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	mov edx, 1
	mov rcx, r14
	mov r8d, 0
	mov r9, r15
	call {vg_blake2b_compress_avx2}
	mov rbx, rdi
	mov r15, r9
	mov r13d, 0
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test r12, r12
	je 213f
	mov rax, r12
	sub rax, 1
	shr rax, 7
	test rax, rax
	je 215f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rax
	mov rcx, r14
	add rcx, 128
	mov r8d, 0
	mov r9, r15
	call {vg_blake2b_compress_avx2}
	mov rbx, rdi
	mov r15, r9
	mov rax, r12
	sub rax, 1
	and rax, 127
	add rax, 1
	sub r12, rax
	add rbp, r12
	add r14, r12
	mov r12, rax
	jmp 216f
215:
216:
	mov rax, r12
	add r14, rax
	mov r12d, 0
217:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6

vg_blake2b_finalize_avx2:
	lea rsp, [rsp-584]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+512], rbx
	mov QWORD PTR [rcx+520], rbp
	mov QWORD PTR [rcx+528], r12
	mov QWORD PTR [rcx+536], r13
	mov QWORD PTR [rcx+544], r14
	mov QWORD PTR [rcx+552], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 127
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	mov r9d, 0
	mov eax, 128
	sub rax, r13
	je 22f
24:
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	sub rax, 1
	jne 24b
	jmp 23f
22:
23:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	mov edx, 1
	mov rcx, r14
	mov r8d, 1
	mov r9, r15
	call {vg_blake2b_compress_avx2}
	mov rbx, rdi
	mov r15, r9
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6

vg_blake2b_update_avx512:
	lea rsp, [rsp-584]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+512], rbx
	mov QWORD PTR [r8+520], rbp
	mov QWORD PTR [r8+528], r12
	mov QWORD PTR [r8+536], r13
	mov QWORD PTR [r8+544], r14
	mov QWORD PTR [r8+552], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 127
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	test r12, r12
	je 22f
	test r13, r13
	je 24f
	mov eax, 128
	sub rax, r13
	cmp r12, rax
	jb 26f
	jmp 27f
26:
	mov rax, r12
27:
	sub r12, rax
	add r14, rax
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	test r12, r12
	je 211f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	mov edx, 1
	mov rcx, r14
	mov r8d, 0
	mov r9, r15
	call {vg_blake2b_compress_avx512}
	mov rbx, rdi
	mov r15, r9
	mov r13d, 0
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test r12, r12
	je 213f
	mov rax, r12
	sub rax, 1
	shr rax, 7
	test rax, rax
	je 215f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rax
	mov rcx, r14
	add rcx, 128
	mov r8d, 0
	mov r9, r15
	call {vg_blake2b_compress_avx512}
	mov rbx, rdi
	mov r15, r9
	mov rax, r12
	sub rax, 1
	and rax, 127
	add rax, 1
	sub r12, rax
	add rbp, r12
	add r14, r12
	mov r12, rax
	jmp 216f
215:
216:
	mov rax, r12
	add r14, rax
	mov r12d, 0
217:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6

vg_blake2b_finalize_avx512:
	lea rsp, [rsp-584]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+512], rbx
	mov QWORD PTR [rcx+520], rbp
	mov QWORD PTR [rcx+528], r12
	mov QWORD PTR [rcx+536], r13
	mov QWORD PTR [rcx+544], r14
	mov QWORD PTR [rcx+552], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 127
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	mov r9d, 0
	mov eax, 128
	sub rax, r13
	je 22f
24:
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	sub rax, 1
	jne 24b
	jmp 23f
22:
23:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	mov edx, 1
	mov rcx, r14
	mov r8d, 1
	mov r9, r15
	call {vg_blake2b_compress_avx512}
	mov rbx, rdi
	mov r15, r9
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6

vg_blake2b_update:
	lea rsp, [rsp-584]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+512], rbx
	mov QWORD PTR [r8+520], rbp
	mov QWORD PTR [r8+528], r12
	mov QWORD PTR [r8+536], r13
	mov QWORD PTR [r8+544], r14
	mov QWORD PTR [r8+552], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 127
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	test r12, r12
	je 22f
	test r13, r13
	je 24f
	mov eax, 128
	sub rax, r13
	cmp r12, rax
	jb 26f
	jmp 27f
26:
	mov rax, r12
27:
	sub r12, rax
	add r14, rax
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	test r12, r12
	je 211f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	mov edx, 1
	mov rcx, r14
	mov r8d, 0
	mov r9, r15
	call {vg_blake2b_compress}
	mov rbx, rdi
	mov r15, r9
	mov r13d, 0
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test r12, r12
	je 213f
	mov rax, r12
	sub rax, 1
	shr rax, 7
	test rax, rax
	je 215f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rax
	mov rcx, r14
	add rcx, 128
	mov r8d, 0
	mov r9, r15
	call {vg_blake2b_compress}
	mov rbx, rdi
	mov r15, r9
	mov rax, r12
	sub rax, 1
	and rax, 127
	add rax, 1
	sub r12, rax
	add rbp, r12
	add r14, r12
	mov r12, rax
	jmp 216f
215:
216:
	mov rax, r12
	add r14, rax
	mov r12d, 0
217:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6

vg_blake2b_finalize:
	lea rsp, [rsp-584]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+512], rbx
	mov QWORD PTR [rcx+520], rbp
	mov QWORD PTR [rcx+528], r12
	mov QWORD PTR [rcx+536], r13
	mov QWORD PTR [rcx+544], r14
	mov QWORD PTR [rcx+552], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 127
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	mov r9d, 0
	mov eax, 128
	sub rax, r13
	je 22f
24:
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	sub rax, 1
	jne 24b
	jmp 23f
22:
23:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 64
	mov edx, 1
	mov rcx, r14
	mov r8d, 1
	mov r9, r15
	call {vg_blake2b_compress}
	mov rbx, rdi
	mov r15, r9
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+56], rax
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6
