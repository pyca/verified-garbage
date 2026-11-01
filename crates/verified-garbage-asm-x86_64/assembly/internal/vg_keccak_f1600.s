// The functions of `src/internal/vg_keccak_f1600.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600:
	mov QWORD PTR [rsi+392], rbx
	mov QWORD PTR [rsi+400], rbp
	mov QWORD PTR [rsi+408], r12
	mov QWORD PTR [rsi+416], r13
	mov QWORD PTR [rsi+424], r14
	mov QWORD PTR [rsi+432], r15
	movabs rax, 1
	mov QWORD PTR [rsi+200], rax
	movabs rax, 32898
	mov QWORD PTR [rsi+208], rax
	movabs rax, -9223372036854742902
	mov QWORD PTR [rsi+216], rax
	movabs rax, -9223372034707259392
	mov QWORD PTR [rsi+224], rax
	movabs rax, 32907
	mov QWORD PTR [rsi+232], rax
	movabs rax, 2147483649
	mov QWORD PTR [rsi+240], rax
	movabs rax, -9223372034707259263
	mov QWORD PTR [rsi+248], rax
	movabs rax, -9223372036854743031
	mov QWORD PTR [rsi+256], rax
	movabs rax, 138
	mov QWORD PTR [rsi+264], rax
	movabs rax, 136
	mov QWORD PTR [rsi+272], rax
	movabs rax, 2147516425
	mov QWORD PTR [rsi+280], rax
	movabs rax, 2147483658
	mov QWORD PTR [rsi+288], rax
	movabs rax, 2147516555
	mov QWORD PTR [rsi+296], rax
	movabs rax, -9223372036854775669
	mov QWORD PTR [rsi+304], rax
	movabs rax, -9223372036854742903
	mov QWORD PTR [rsi+312], rax
	movabs rax, -9223372036854743037
	mov QWORD PTR [rsi+320], rax
	movabs rax, -9223372036854743038
	mov QWORD PTR [rsi+328], rax
	movabs rax, -9223372036854775680
	mov QWORD PTR [rsi+336], rax
	movabs rax, 32778
	mov QWORD PTR [rsi+344], rax
	movabs rax, -9223372034707292150
	mov QWORD PTR [rsi+352], rax
	movabs rax, -9223372034707259263
	mov QWORD PTR [rsi+360], rax
	movabs rax, -9223372036854742912
	mov QWORD PTR [rsi+368], rax
	movabs rax, 2147483649
	mov QWORD PTR [rsi+376], rax
	movabs rax, -9223372034707259384
	mov QWORD PTR [rsi+384], rax
	mov r15, -192
	mov rax, QWORD PTR [rdi+8]
	xor rax, -1
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	xor rax, -1
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+64]
	xor rax, -1
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+96]
	xor rax, -1
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+136]
	xor rax, -1
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+160]
	xor rax, -1
	mov QWORD PTR [rdi+160], rax
	mov rbx, QWORD PTR [rdi+168]
	mov rcx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+184]
	mov rbp, QWORD PTR [rdi+192]
20:
	mov r8, QWORD PTR [rdi]
	mov r9, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+144]
	xor rcx, QWORD PTR [rdi+16]
	xor rdx, QWORD PTR [rdi+24]
	xor rax, r8
	xor rbx, QWORD PTR [rdi+8]
	xor rcx, QWORD PTR [rdi+56]
	xor rax, QWORD PTR [rdi+40]
	mov r12, rbp
	xor rbp, QWORD PTR [rdi+32]
	xor rcx, r10
	xor rax, QWORD PTR [rdi+80]
	xor rdx, QWORD PTR [rdi+64]
	xor rbx, r9
	xor rbp, QWORD PTR [rdi+72]
	xor rcx, QWORD PTR [rdi+136]
	xor rax, QWORD PTR [rdi+120]
	xor rdx, QWORD PTR [rdi+104]
	xor rbx, QWORD PTR [rdi+88]
	xor rbp, QWORD PTR [rdi+112]
	mov r13, rcx
	ror rcx, 63
	xor rcx, rax
	xor rdx, r11
	ror rax, 63
	xor rax, rdx
	xor rbx, QWORD PTR [rdi+128]
	ror rdx, 63
	xor rdx, rbx
	xor rbp, QWORD PTR [rdi+152]
	ror rbx, 63
	xor rbx, rbp
	ror rbp, 63
	xor rbp, r13
	xor r9, rcx
	xor r10, rdx
	ror r9, 20
	xor r11, rbp
	xor r12, rax
	ror r10, 21
	xor r8, rbx
	mov r13, r9
	ror r11, 43
	or r9, r10
	xor r9, r8
	ror r12, 50
	xor r9, QWORD PTR [rsi+r15*1+392]
	mov r14, r12
	and r12, r11
	mov QWORD PTR [rsi], r9
	xor r12, r10
	xor r10, -1
	mov QWORD PTR [rsi+16], r12
	or r10, r11
	mov r12, QWORD PTR [rdi+176]
	xor r10, r13
	mov QWORD PTR [rsi+8], r10
	and r13, r8
	mov r9, QWORD PTR [rdi+72]
	xor r13, r14
	mov r10, QWORD PTR [rdi+80]
	mov QWORD PTR [rsi+32], r13
	or r14, r8
	mov r8, QWORD PTR [rdi+24]
	xor r14, r11
	mov r11, QWORD PTR [rdi+128]
	mov QWORD PTR [rsi+24], r14
	xor r8, rbp
	xor r12, rdx
	ror r8, 36
	xor r11, rcx
	xor r9, rax
	ror r12, 3
	ror r11, 19
	xor r10, rbx
	ror r9, 44
	mov r13, r8
	or r8, r12
	ror r10, 61
	xor r8, r11
	mov QWORD PTR [rsi+64], r8
	mov r14, r9
	and r9, r13
	mov r8, QWORD PTR [rdi+8]
	xor r9, r12
	xor r12, -1
	mov QWORD PTR [rsi+72], r9
	or r12, r11
	mov r9, QWORD PTR [rdi+56]
	xor r12, r10
	mov QWORD PTR [rsi+56], r12
	and r11, r10
	mov r12, QWORD PTR [rdi+160]
	xor r11, r14
	mov QWORD PTR [rsi+48], r11
	or r14, r10
	mov r10, QWORD PTR [rdi+104]
	xor r14, r13
	mov r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rsi+40], r14
	xor r10, rbp
	xor r11, rax
	ror r10, 39
	xor r9, rdx
	ror r11, 56
	xor r12, rbx
	ror r9, 58
	xor r8, rcx
	ror r12, 46
	mov r13, r10
	and r10, r11
	ror r8, 63
	xor r11, -1
	xor r10, r9
	mov QWORD PTR [rsi+88], r10
	mov r14, r12
	and r12, r11
	mov r10, QWORD PTR [rdi+88]
	xor r12, r13
	mov QWORD PTR [rsi+96], r12
	or r13, r9
	mov r12, QWORD PTR [rdi+184]
	xor r13, r8
	mov QWORD PTR [rsi+80], r13
	and r9, r8
	xor r9, r14
	mov QWORD PTR [rsi+112], r9
	or r14, r8
	mov r9, QWORD PTR [rdi+40]
	xor r14, r11
	mov r11, QWORD PTR [rdi+136]
	mov QWORD PTR [rsi+104], r14
	mov r8, QWORD PTR [rdi+32]
	xor r10, rcx
	xor r11, rdx
	ror r10, 54
	xor r9, rbx
	ror r11, 49
	xor r12, rbp
	ror r9, 28
	xor r8, rax
	ror r12, 8
	mov r13, r10
	or r10, r11
	ror r8, 37
	xor r11, -1
	xor r10, r9
	mov QWORD PTR [rsi+128], r10
	mov r14, r12
	or r12, r11
	xor r12, r13
	mov QWORD PTR [rsi+136], r12
	and r13, r9
	xor r13, r8
	mov QWORD PTR [rsi+120], r13
	or r9, r8
	xor r9, r14
	mov QWORD PTR [rsi+152], r9
	and r8, r14
	xor r8, r11
	mov QWORD PTR [rsi+144], r8
	xor rdx, QWORD PTR [rdi+16]
	xor rbp, QWORD PTR [rdi+64]
	ror rdx, 2
	xor rcx, QWORD PTR [rdi+168]
	ror rbp, 9
	xor rax, QWORD PTR [rdi+112]
	ror rcx, 62
	xor rbx, QWORD PTR [rdi+120]
	ror rax, 25
	ror rbx, 23
	mov r13, rdx
	and rdx, rbp
	xor rbp, -1
	xor rdx, rcx
	mov QWORD PTR [rsi+192], rdx
	mov r14, rax
	and rax, rbp
	xor rax, r13
	mov QWORD PTR [rsi+160], rax
	or r13, rcx
	xor r13, rbx
	mov QWORD PTR [rsi+184], r13
	and rcx, rbx
	xor rcx, r14
	mov QWORD PTR [rsi+176], rcx
	or rbx, r14
	xor rbx, rbp
	mov QWORD PTR [rsi+168], rbx
	mov rbp, rdx
	mov rdx, r13
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+48]
	mov r10, QWORD PTR [rsi+96]
	mov r11, QWORD PTR [rsi+144]
	xor rcx, QWORD PTR [rsi+16]
	xor rdx, QWORD PTR [rsi+24]
	xor rax, r8
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rsi+40]
	mov r12, rbp
	xor rbp, QWORD PTR [rsi+32]
	xor rcx, r10
	xor rax, QWORD PTR [rsi+80]
	xor rdx, QWORD PTR [rsi+64]
	xor rbx, r9
	xor rbp, QWORD PTR [rsi+72]
	xor rcx, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rsi+120]
	xor rdx, QWORD PTR [rsi+104]
	xor rbx, QWORD PTR [rsi+88]
	xor rbp, QWORD PTR [rsi+112]
	mov r13, rcx
	ror rcx, 63
	xor rcx, rax
	xor rdx, r11
	ror rax, 63
	xor rax, rdx
	xor rbx, QWORD PTR [rsi+128]
	ror rdx, 63
	xor rdx, rbx
	xor rbp, QWORD PTR [rsi+152]
	ror rbx, 63
	xor rbx, rbp
	ror rbp, 63
	xor rbp, r13
	xor r9, rcx
	xor r10, rdx
	ror r9, 20
	xor r11, rbp
	xor r12, rax
	ror r10, 21
	xor r8, rbx
	mov r13, r9
	ror r11, 43
	or r9, r10
	xor r9, r8
	ror r12, 50
	xor r9, QWORD PTR [rsi+r15*1+400]
	mov r14, r12
	and r12, r11
	mov QWORD PTR [rdi], r9
	xor r12, r10
	xor r10, -1
	mov QWORD PTR [rdi+16], r12
	or r10, r11
	mov r12, QWORD PTR [rsi+176]
	xor r10, r13
	mov QWORD PTR [rdi+8], r10
	and r13, r8
	mov r9, QWORD PTR [rsi+72]
	xor r13, r14
	mov r10, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+32], r13
	or r14, r8
	mov r8, QWORD PTR [rsi+24]
	xor r14, r11
	mov r11, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+24], r14
	xor r8, rbp
	xor r12, rdx
	ror r8, 36
	xor r11, rcx
	xor r9, rax
	ror r12, 3
	ror r11, 19
	xor r10, rbx
	ror r9, 44
	mov r13, r8
	or r8, r12
	ror r10, 61
	xor r8, r11
	mov QWORD PTR [rdi+64], r8
	mov r14, r9
	and r9, r13
	mov r8, QWORD PTR [rsi+8]
	xor r9, r12
	xor r12, -1
	mov QWORD PTR [rdi+72], r9
	or r12, r11
	mov r9, QWORD PTR [rsi+56]
	xor r12, r10
	mov QWORD PTR [rdi+56], r12
	and r11, r10
	mov r12, QWORD PTR [rsi+160]
	xor r11, r14
	mov QWORD PTR [rdi+48], r11
	or r14, r10
	mov r10, QWORD PTR [rsi+104]
	xor r14, r13
	mov r11, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+40], r14
	xor r10, rbp
	xor r11, rax
	ror r10, 39
	xor r9, rdx
	ror r11, 56
	xor r12, rbx
	ror r9, 58
	xor r8, rcx
	ror r12, 46
	mov r13, r10
	and r10, r11
	ror r8, 63
	xor r11, -1
	xor r10, r9
	mov QWORD PTR [rdi+88], r10
	mov r14, r12
	and r12, r11
	mov r10, QWORD PTR [rsi+88]
	xor r12, r13
	mov QWORD PTR [rdi+96], r12
	or r13, r9
	mov r12, QWORD PTR [rsi+184]
	xor r13, r8
	mov QWORD PTR [rdi+80], r13
	and r9, r8
	xor r9, r14
	mov QWORD PTR [rdi+112], r9
	or r14, r8
	mov r9, QWORD PTR [rsi+40]
	xor r14, r11
	mov r11, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+104], r14
	mov r8, QWORD PTR [rsi+32]
	xor r10, rcx
	xor r11, rdx
	ror r10, 54
	xor r9, rbx
	ror r11, 49
	xor r12, rbp
	ror r9, 28
	xor r8, rax
	ror r12, 8
	mov r13, r10
	or r10, r11
	ror r8, 37
	xor r11, -1
	xor r10, r9
	mov QWORD PTR [rdi+128], r10
	mov r14, r12
	or r12, r11
	xor r12, r13
	mov QWORD PTR [rdi+136], r12
	and r13, r9
	xor r13, r8
	mov QWORD PTR [rdi+120], r13
	or r9, r8
	xor r9, r14
	mov QWORD PTR [rdi+152], r9
	and r8, r14
	xor r8, r11
	mov QWORD PTR [rdi+144], r8
	xor rdx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+64]
	ror rdx, 2
	xor rcx, QWORD PTR [rsi+168]
	ror rbp, 9
	xor rax, QWORD PTR [rsi+112]
	ror rcx, 62
	xor rbx, QWORD PTR [rsi+120]
	ror rax, 25
	ror rbx, 23
	mov r13, rdx
	and rdx, rbp
	xor rbp, -1
	xor rdx, rcx
	mov QWORD PTR [rdi+192], rdx
	mov r14, rax
	and rax, rbp
	xor rax, r13
	mov QWORD PTR [rdi+160], rax
	or r13, rcx
	xor r13, rbx
	mov QWORD PTR [rdi+184], r13
	and rcx, rbx
	xor rcx, r14
	mov QWORD PTR [rdi+176], rcx
	or rbx, r14
	xor rbx, rbp
	mov QWORD PTR [rdi+168], rbx
	mov rbp, rdx
	mov rdx, r13
	add r15, 16
	jne 20b
	mov rax, QWORD PTR [rdi+8]
	xor rax, -1
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+16]
	xor rax, -1
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+64]
	xor rax, -1
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+96]
	xor rax, -1
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+136]
	xor rax, -1
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+160]
	xor rax, -1
	mov QWORD PTR [rdi+160], rax
	mov rbx, QWORD PTR [rsi+392]
	mov rbp, QWORD PTR [rsi+400]
	mov r12, QWORD PTR [rsi+408]
	mov r13, QWORD PTR [rsi+416]
	mov r14, QWORD PTR [rsi+424]
	mov r15, QWORD PTR [rsi+432]
	ret
	.p2align 6
