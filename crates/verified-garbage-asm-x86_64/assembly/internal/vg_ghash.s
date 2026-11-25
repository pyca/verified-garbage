// The functions of `src/internal/vg_ghash.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	mov QWORD PTR [r8+152], rbx
	mov QWORD PTR [r8+160], rbp
	mov QWORD PTR [r8+168], r12
	mov QWORD PTR [r8+176], r13
	mov QWORD PTR [r8+184], r14
	mov QWORD PTR [r8+192], r15
	mov r15, rdx
	mov r9, QWORD PTR [rdi]
	mov r10, QWORD PTR [rdi+8]
	mov rdi, rcx
	bswap r9
	bswap r10
	mov r11, r9
	shr r11, 63
	mov r14, r10
	shr r14, 63
	shl r9, 1
	xor r9, r14
	shl r10, 1
	xor r10, r11
	shl r11, 57
	xor r9, r11
	shl r11, 5
	xor r9, r11
	shl r11, 1
	xor r9, r11
	mov r11, r9
	xor r11, r10
	movabs rax, 1190112520884487201
	and rax, r10
	mov QWORD PTR [r8], rax
	movabs rax, 2380225041768974402
	and rax, r10
	mov QWORD PTR [r8+8], rax
	movabs rax, 4760450083537948804
	and rax, r10
	mov QWORD PTR [r8+16], rax
	movabs rax, -8925843906633654008
	and rax, r10
	mov QWORD PTR [r8+24], rax
	movabs rax, 595056260442243600
	and rax, r10
	mov QWORD PTR [r8+32], rax
	movabs rax, 1190112520884487201
	and rax, r9
	mov QWORD PTR [r8+40], rax
	movabs rax, 2380225041768974402
	and rax, r9
	mov QWORD PTR [r8+48], rax
	movabs rax, 4760450083537948804
	and rax, r9
	mov QWORD PTR [r8+56], rax
	movabs rax, -8925843906633654008
	and rax, r9
	mov QWORD PTR [r8+64], rax
	movabs rax, 595056260442243600
	and rax, r9
	mov QWORD PTR [r8+72], rax
	movabs rax, 1190112520884487201
	and rax, r11
	mov QWORD PTR [r8+80], rax
	movabs rax, 2380225041768974402
	and rax, r11
	mov QWORD PTR [r8+88], rax
	movabs rax, 4760450083537948804
	and rax, r11
	mov QWORD PTR [r8+96], rax
	movabs rax, -8925843906633654008
	and rax, r11
	mov QWORD PTR [r8+104], rax
	movabs rax, 595056260442243600
	and rax, r11
	mov QWORD PTR [r8+112], rax
	mov r9, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	bswap r9
	bswap r10
	mov QWORD PTR [r8+200], r9
	mov QWORD PTR [r8+208], r10
	test rdi, rdi
	je 20f
22:
	mov r9, QWORD PTR [r15]
	mov r10, QWORD PTR [r15+8]
	bswap r9
	bswap r10
	xor r9, QWORD PTR [r8+200]
	xor r10, QWORD PTR [r8+208]
	mov QWORD PTR [r8+200], r9
	mov QWORD PTR [r8+208], r10
	xor r9, r10
	mov QWORD PTR [r8+216], r9
	movabs rcx, 1190112520884487201
	and rcx, QWORD PTR [r8+208]
	movabs rbx, 2380225041768974402
	and rbx, QWORD PTR [r8+208]
	movabs rbp, 4760450083537948804
	and rbp, QWORD PTR [r8+208]
	movabs r12, -8925843906633654008
	and r12, QWORD PTR [r8+208]
	movabs r13, 595056260442243600
	and r13, QWORD PTR [r8+208]
	xor r11, r11
	xor r14, r14
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+32]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+24]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+16]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+8]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 1190112520884487201
	and r9, rax
	movabs rdx, 2380225041768974402
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+8]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+32]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+24]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+16]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 2380225041768974402
	and r9, rax
	movabs rdx, 4760450083537948804
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+16]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+8]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+32]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+24]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 4760450083537948804
	and r9, rax
	movabs rdx, -8925843906633654008
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+24]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+16]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+8]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+32]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, -8925843906633654008
	and r9, rax
	movabs rdx, 595056260442243600
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+32]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+24]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+16]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+8]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 595056260442243600
	and r9, rax
	movabs rdx, 1190112520884487201
	and r10, rdx
	xor r11, r9
	xor r14, r10
	mov QWORD PTR [r8+120], r11
	mov QWORD PTR [r8+128], r14
	movabs rcx, 1190112520884487201
	and rcx, QWORD PTR [r8+200]
	movabs rbx, 2380225041768974402
	and rbx, QWORD PTR [r8+200]
	movabs rbp, 4760450083537948804
	and rbp, QWORD PTR [r8+200]
	movabs r12, -8925843906633654008
	and r12, QWORD PTR [r8+200]
	movabs r13, 595056260442243600
	and r13, QWORD PTR [r8+200]
	xor r11, r11
	xor r14, r14
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+40]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+72]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+64]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+56]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+48]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 1190112520884487201
	and r9, rax
	movabs rdx, 2380225041768974402
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+48]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+40]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+72]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+64]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+56]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 2380225041768974402
	and r9, rax
	movabs rdx, 4760450083537948804
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+56]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+48]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+40]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+72]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+64]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 4760450083537948804
	and r9, rax
	movabs rdx, -8925843906633654008
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+64]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+56]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+48]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+40]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+72]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, -8925843906633654008
	and r9, rax
	movabs rdx, 595056260442243600
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+72]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+64]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+56]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+48]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+40]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 595056260442243600
	and r9, rax
	movabs rdx, 1190112520884487201
	and r10, rdx
	xor r11, r9
	xor r14, r10
	mov QWORD PTR [r8+136], r11
	mov QWORD PTR [r8+144], r14
	movabs rcx, 1190112520884487201
	and rcx, QWORD PTR [r8+216]
	movabs rbx, 2380225041768974402
	and rbx, QWORD PTR [r8+216]
	movabs rbp, 4760450083537948804
	and rbp, QWORD PTR [r8+216]
	movabs r12, -8925843906633654008
	and r12, QWORD PTR [r8+216]
	movabs r13, 595056260442243600
	and r13, QWORD PTR [r8+216]
	xor r11, r11
	xor r14, r14
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+80]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+112]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+104]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+96]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+88]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 1190112520884487201
	and r9, rax
	movabs rdx, 2380225041768974402
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+88]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+80]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+112]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+104]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+96]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 2380225041768974402
	and r9, rax
	movabs rdx, 4760450083537948804
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+96]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+88]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+80]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+112]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+104]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 4760450083537948804
	and r9, rax
	movabs rdx, -8925843906633654008
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+104]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+96]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+88]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+80]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+112]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, -8925843906633654008
	and r9, rax
	movabs rdx, 595056260442243600
	and r10, rdx
	xor r11, r9
	xor r14, r10
	xor r9, r9
	xor r10, r10
	mov rax, QWORD PTR [r8+112]
	mul rcx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+104]
	mul rbx
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+96]
	mul rbp
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+88]
	mul r12
	xor r9, rax
	xor r10, rdx
	mov rax, QWORD PTR [r8+80]
	mul r13
	xor r9, rax
	xor r10, rdx
	movabs rax, 595056260442243600
	and r9, rax
	movabs rdx, 1190112520884487201
	and r10, rdx
	xor r11, r9
	xor r14, r10
	mov rax, QWORD PTR [r8+120]
	mov rdx, QWORD PTR [r8+128]
	mov rcx, QWORD PTR [r8+136]
	mov rbx, QWORD PTR [r8+144]
	xor r11, rax
	xor r11, rcx
	xor r14, rdx
	xor r14, rbx
	xor r11, rdx
	xor r14, rcx
	xor r14, rax
	mov r9, rax
	shl r9, 57
	xor r11, r9
	shl r9, 5
	xor r11, r9
	shl r9, 1
	xor r11, r9
	mov r9, rax
	shr r9, 1
	xor r14, r9
	shr r9, 1
	xor r14, r9
	shr r9, 5
	xor r14, r9
	xor rbx, r11
	mov r9, r11
	shr r9, 1
	xor rbx, r9
	shr r9, 1
	xor rbx, r9
	shr r9, 5
	xor rbx, r9
	mov r9, r11
	shl r9, 57
	xor r14, r9
	shl r9, 5
	xor r14, r9
	shl r9, 1
	xor r14, r9
	mov QWORD PTR [r8+200], rbx
	mov QWORD PTR [r8+208], r14
	add r15, 16
	sub rdi, 1
	jne 22b
	jmp 21f
20:
21:
	mov r9, QWORD PTR [r8+200]
	mov r10, QWORD PTR [r8+208]
	bswap r9
	bswap r10
	mov rbx, QWORD PTR [r8+152]
	mov rbp, QWORD PTR [r8+160]
	mov r12, QWORD PTR [r8+168]
	mov r13, QWORD PTR [r8+176]
	mov r14, QWORD PTR [r8+184]
	mov r15, QWORD PTR [r8+192]
	mov QWORD PTR [rsi], r9
	mov QWORD PTR [rsi+8], r10
	ret
	.p2align 6
