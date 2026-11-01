// The functions of `src/internal/vg_ghash.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r11, QWORD PTR [rdi]
	bswap r11
	mov r12, QWORD PTR [rdi+8]
	bswap r12
	add r12, r12
	adc r11, r11
	sbb rax, rax
	movabs r13, -4467570830351532032
	and r13, rax
	xor r11, r13
	and rax, 1
	xor r12, rax
	mov r14, r11
	xor r14, r12
	movabs rax, 286331153
	and rax, r11
	mov QWORD PTR [r8+48], rax
	movabs rax, 1229782937960972288
	and rax, r11
	mov QWORD PTR [r8+56], rax
	movabs rax, 572662306
	and rax, r11
	mov QWORD PTR [r8+64], rax
	movabs rax, 2459565875921944576
	and rax, r11
	mov QWORD PTR [r8+72], rax
	movabs rax, 1145324612
	and rax, r11
	mov QWORD PTR [r8+80], rax
	movabs rax, 4919131751843889152
	and rax, r11
	mov QWORD PTR [r8+88], rax
	movabs rax, 2290649224
	and rax, r11
	mov QWORD PTR [r8+96], rax
	movabs rax, -8608480570021773312
	and rax, r11
	mov QWORD PTR [r8+104], rax
	movabs rax, 286331153
	and rax, r12
	mov QWORD PTR [r8+112], rax
	movabs rax, 1229782937960972288
	and rax, r12
	mov QWORD PTR [r8+120], rax
	movabs rax, 572662306
	and rax, r12
	mov QWORD PTR [r8+128], rax
	movabs rax, 2459565875921944576
	and rax, r12
	mov QWORD PTR [r8+136], rax
	movabs rax, 1145324612
	and rax, r12
	mov QWORD PTR [r8+144], rax
	movabs rax, 4919131751843889152
	and rax, r12
	mov QWORD PTR [r8+152], rax
	movabs rax, 2290649224
	and rax, r12
	mov QWORD PTR [r8+160], rax
	movabs rax, -8608480570021773312
	and rax, r12
	mov QWORD PTR [r8+168], rax
	movabs rax, 286331153
	and rax, r14
	mov QWORD PTR [r8+176], rax
	movabs rax, 1229782937960972288
	and rax, r14
	mov QWORD PTR [r8+184], rax
	movabs rax, 572662306
	and rax, r14
	mov QWORD PTR [r8+192], rax
	movabs rax, 2459565875921944576
	and rax, r14
	mov QWORD PTR [r8+200], rax
	movabs rax, 1145324612
	and rax, r14
	mov QWORD PTR [r8+208], rax
	movabs rax, 4919131751843889152
	and rax, r14
	mov QWORD PTR [r8+216], rax
	movabs rax, 2290649224
	and rax, r14
	mov QWORD PTR [r8+224], rax
	movabs rax, -8608480570021773312
	and rax, r14
	mov QWORD PTR [r8+232], rax
	mov rdi, rdx
	test rcx, rcx
	je 20f
22:
	mov r15, QWORD PTR [rsi]
	bswap r15
	mov rax, QWORD PTR [rdi]
	bswap rax
	xor r15, rax
	mov r11, QWORD PTR [rsi+8]
	bswap r11
	mov rax, QWORD PTR [rdi+8]
	bswap rax
	xor r11, rax
	mov QWORD PTR [rsi+8], r11
	xor r11, r15
	mov QWORD PTR [r8+240], r11
	movabs rbx, 1229782938247303441
	and rbx, r15
	movabs rbp, 2459565876494606882
	and rbp, r15
	movabs r9, 4919131752989213764
	and r9, r15
	movabs r10, -8608480567731124088
	and r10, r15
	mov r13, 0
	mov r14, 0
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+48]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+56]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+64]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+72]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+80]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+88]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+96]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+104]
	mul rbp
	xor r11, rax
	xor r12, rdx
	movabs rax, 1229782938247303441
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+48]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+56]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+64]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+72]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+80]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+88]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+96]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+104]
	mul r9
	xor r11, rax
	xor r12, rdx
	movabs rax, 2459565876494606882
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+48]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+56]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+64]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+72]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+80]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+88]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+96]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+104]
	mul r10
	xor r11, rax
	xor r12, rdx
	movabs rax, 4919131752989213764
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+48]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+56]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+64]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+72]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+80]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+88]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+96]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+104]
	mul rbx
	xor r11, rax
	xor r12, rdx
	movabs rax, -8608480567731124088
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r15, r14
	mov QWORD PTR [rsi], r13
	movabs rbx, 1229782938247303441
	and rbx, QWORD PTR [rsi+8]
	movabs rbp, 2459565876494606882
	and rbp, QWORD PTR [rsi+8]
	movabs r9, 4919131752989213764
	and r9, QWORD PTR [rsi+8]
	movabs r10, -8608480567731124088
	and r10, QWORD PTR [rsi+8]
	mov r13, 0
	mov r14, 0
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+112]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+120]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+128]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+136]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+144]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+152]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+160]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+168]
	mul rbp
	xor r11, rax
	xor r12, rdx
	movabs rax, 1229782938247303441
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+112]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+120]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+128]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+136]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+144]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+152]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+160]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+168]
	mul r9
	xor r11, rax
	xor r12, rdx
	movabs rax, 2459565876494606882
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+112]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+120]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+128]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+136]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+144]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+152]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+160]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+168]
	mul r10
	xor r11, rax
	xor r12, rdx
	movabs rax, 4919131752989213764
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+112]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+120]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+128]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+136]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+144]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+152]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+160]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+168]
	mul rbx
	xor r11, rax
	xor r12, rdx
	movabs rax, -8608480567731124088
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov rax, QWORD PTR [rsi]
	xor rax, r14
	mov r11, rax
	xor r11, r15
	xor rax, r13
	mov QWORD PTR [rsi], r11
	mov QWORD PTR [rsi+8], rax
	mov QWORD PTR [r8+248], r13
	movabs rbx, 1229782938247303441
	and rbx, QWORD PTR [r8+240]
	movabs rbp, 2459565876494606882
	and rbp, QWORD PTR [r8+240]
	movabs r9, 4919131752989213764
	and r9, QWORD PTR [r8+240]
	movabs r10, -8608480567731124088
	and r10, QWORD PTR [r8+240]
	mov r13, 0
	mov r14, 0
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+176]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+184]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+192]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+200]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+208]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+216]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+224]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+232]
	mul rbp
	xor r11, rax
	xor r12, rdx
	movabs rax, 1229782938247303441
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+176]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+184]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+192]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+200]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+208]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+216]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+224]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+232]
	mul r9
	xor r11, rax
	xor r12, rdx
	movabs rax, 2459565876494606882
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+176]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+184]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+192]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+200]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+208]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+216]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+224]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+232]
	mul r10
	xor r11, rax
	xor r12, rdx
	movabs rax, 4919131752989213764
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, 0
	mov r12, 0
	mov rax, QWORD PTR [r8+176]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+184]
	mul r10
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+192]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+200]
	mul r9
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+208]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+216]
	mul rbp
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+224]
	mul rbx
	xor r11, rax
	xor r12, rdx
	mov rax, QWORD PTR [r8+232]
	mul rbx
	xor r11, rax
	xor r12, rdx
	movabs rax, -8608480567731124088
	and r11, rax
	and r12, rax
	xor r13, r11
	xor r14, r12
	mov r11, QWORD PTR [rsi]
	xor r11, r14
	mov r12, QWORD PTR [rsi+8]
	xor r12, r13
	mov r13, QWORD PTR [r8+248]
	xor r11, r13
	mov rax, r13
	shr rax, 1
	xor r11, rax
	mov rax, r13
	shr rax, 2
	xor r11, rax
	mov rax, r13
	shr rax, 7
	xor r11, rax
	mov rax, r13
	and rax, 1
	ror rax, 1
	xor r12, rax
	mov rax, r13
	and rax, 3
	ror rax, 2
	xor r12, rax
	mov rax, r13
	and rax, 127
	ror rax, 7
	xor r12, rax
	xor r15, r12
	mov rax, r12
	shr rax, 1
	xor r15, rax
	mov rax, r12
	shr rax, 2
	xor r15, rax
	mov rax, r12
	shr rax, 7
	xor r15, rax
	mov rax, r12
	and rax, 1
	ror rax, 1
	xor r11, rax
	mov rax, r12
	and rax, 3
	ror rax, 2
	xor r11, rax
	mov rax, r12
	and rax, 127
	ror rax, 7
	xor r11, rax
	bswap r15
	mov QWORD PTR [rsi], r15
	bswap r11
	mov QWORD PTR [rsi+8], r11
	add rdi, 16
	sub rcx, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r8]
	mov rbp, QWORD PTR [r8+8]
	mov r12, QWORD PTR [r8+16]
	mov r13, QWORD PTR [r8+24]
	mov r14, QWORD PTR [r8+32]
	mov r15, QWORD PTR [r8+40]
	ret
	.p2align 6
