// The functions of `src/internal/vg_seed_decrypt_blocks.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_decrypt_blocks:
	mov r9, rcx
	mov QWORD PTR [r9+1000], rbx
	mov QWORD PTR [r9+1008], rbp
	mov QWORD PTR [r9+1016], r12
	mov QWORD PTR [r9+1024], r13
	mov QWORD PTR [r9+1032], r14
	mov QWORD PTR [r9+1040], r15
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+384], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+392], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+400], r14
	movabs r14, -71777214294589696
	mov QWORD PTR [r9+408], r14
	movabs r14, 1095216660735
	mov QWORD PTR [r9+416], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+424], r14
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+432], r14
	movabs r14, 281470681808895
	mov QWORD PTR [r9+440], r14
	movabs r14, -1789082251201616085
	mov QWORD PTR [r9+448], r14
	add rdi, 120
	cmp rdx, 0
	je 20f
22:
	mov rcx, rdx
	cmp rcx, 16
	jb 23f
	mov rcx, 16
	jmp 24f
23:
24:
	mov r10, rsi
	mov rbx, r9
25:
	mov eax, DWORD PTR [r10]
	bswap eax
	mov DWORD PTR [rbx+744], eax
	mov eax, DWORD PTR [r10+4]
	bswap eax
	mov DWORD PTR [rbx+808], eax
	mov eax, DWORD PTR [r10+8]
	bswap eax
	mov DWORD PTR [rbx+872], eax
	mov eax, DWORD PTR [r10+12]
	bswap eax
	mov DWORD PTR [rbx+936], eax
	add r10, 16
	add rbx, 4
	sub rcx, 1
	jne 25b
	mov r8, 16
26:
	mov r11d, DWORD PTR [rdi]
	mov r12d, DWORD PTR [rdi+4]
	mov eax, DWORD PTR [r9+872]
	xor eax, r11d
	mov DWORD PTR [r9+552], eax
	xor eax, DWORD PTR [r9+936]
	xor eax, r12d
	mov DWORD PTR [r9+488], eax
	mov eax, DWORD PTR [r9+876]
	xor eax, r11d
	mov DWORD PTR [r9+556], eax
	xor eax, DWORD PTR [r9+940]
	xor eax, r12d
	mov DWORD PTR [r9+492], eax
	mov eax, DWORD PTR [r9+880]
	xor eax, r11d
	mov DWORD PTR [r9+560], eax
	xor eax, DWORD PTR [r9+944]
	xor eax, r12d
	mov DWORD PTR [r9+496], eax
	mov eax, DWORD PTR [r9+884]
	xor eax, r11d
	mov DWORD PTR [r9+564], eax
	xor eax, DWORD PTR [r9+948]
	xor eax, r12d
	mov DWORD PTR [r9+500], eax
	mov eax, DWORD PTR [r9+888]
	xor eax, r11d
	mov DWORD PTR [r9+568], eax
	xor eax, DWORD PTR [r9+952]
	xor eax, r12d
	mov DWORD PTR [r9+504], eax
	mov eax, DWORD PTR [r9+892]
	xor eax, r11d
	mov DWORD PTR [r9+572], eax
	xor eax, DWORD PTR [r9+956]
	xor eax, r12d
	mov DWORD PTR [r9+508], eax
	mov eax, DWORD PTR [r9+896]
	xor eax, r11d
	mov DWORD PTR [r9+576], eax
	xor eax, DWORD PTR [r9+960]
	xor eax, r12d
	mov DWORD PTR [r9+512], eax
	mov eax, DWORD PTR [r9+900]
	xor eax, r11d
	mov DWORD PTR [r9+580], eax
	xor eax, DWORD PTR [r9+964]
	xor eax, r12d
	mov DWORD PTR [r9+516], eax
	mov eax, DWORD PTR [r9+904]
	xor eax, r11d
	mov DWORD PTR [r9+584], eax
	xor eax, DWORD PTR [r9+968]
	xor eax, r12d
	mov DWORD PTR [r9+520], eax
	mov eax, DWORD PTR [r9+908]
	xor eax, r11d
	mov DWORD PTR [r9+588], eax
	xor eax, DWORD PTR [r9+972]
	xor eax, r12d
	mov DWORD PTR [r9+524], eax
	mov eax, DWORD PTR [r9+912]
	xor eax, r11d
	mov DWORD PTR [r9+592], eax
	xor eax, DWORD PTR [r9+976]
	xor eax, r12d
	mov DWORD PTR [r9+528], eax
	mov eax, DWORD PTR [r9+916]
	xor eax, r11d
	mov DWORD PTR [r9+596], eax
	xor eax, DWORD PTR [r9+980]
	xor eax, r12d
	mov DWORD PTR [r9+532], eax
	mov eax, DWORD PTR [r9+920]
	xor eax, r11d
	mov DWORD PTR [r9+600], eax
	xor eax, DWORD PTR [r9+984]
	xor eax, r12d
	mov DWORD PTR [r9+536], eax
	mov eax, DWORD PTR [r9+924]
	xor eax, r11d
	mov DWORD PTR [r9+604], eax
	xor eax, DWORD PTR [r9+988]
	xor eax, r12d
	mov DWORD PTR [r9+540], eax
	mov eax, DWORD PTR [r9+928]
	xor eax, r11d
	mov DWORD PTR [r9+608], eax
	xor eax, DWORD PTR [r9+992]
	xor eax, r12d
	mov DWORD PTR [r9+544], eax
	mov eax, DWORD PTR [r9+932]
	xor eax, r11d
	mov DWORD PTR [r9+612], eax
	xor eax, DWORD PTR [r9+996]
	xor eax, r12d
	mov DWORD PTR [r9+548], eax
	mov rax, QWORD PTR [r9+488]
	mov rbp, QWORD PTR [r9+496]
	mov r10, QWORD PTR [r9+504]
	mov r12, QWORD PTR [r9+512]
	mov r11, QWORD PTR [r9+520]
	mov r13, QWORD PTR [r9+528]
	mov rbx, QWORD PTR [r9+536]
	mov rcx, QWORD PTR [r9+544]
	mov r14, rax
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, r10
	shr r14, 4
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	ror r14, 60
	xor r10, r14
	mov r14, r12
	shr r14, 4
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	ror r14, 60
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, r10
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbp
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	ror r14, 62
	xor rbp, r14
	mov r14, r11
	shr r14, 2
	xor r14, rbx
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	ror r14, 62
	xor r11, r14
	mov r14, r13
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	ror r14, 62
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	ror r14, 63
	xor rax, r14
	mov r14, r10
	shr r14, 1
	xor r14, r12
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	ror r14, 63
	xor r10, r14
	mov r14, r11
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r11, r14
	mov r14, rbx
	shr r14, 1
	xor r14, rcx
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	ror r14, 63
	xor rbx, r14
	xor r13, r11
	xor rcx, r13
	xor rax, r12
	xor rax, rbp
	xor rbp, r11
	xor r11, r12
	xor r12, r13
	xor r13, rbx
	xor rbx, rcx
	xor r12, r10
	xor rbx, r12
	xor r10, rbp
	xor rbp, r12
	movabs r14, -1
	mov QWORD PTR [r9], r14
	xor rcx, r11
	mov r14, rcx
	xor r14, rbx
	mov r15, r14
	xor r15, r12
	xor rax, r14
	xor rbp, r15
	xor rbp, r13
	mov QWORD PTR [r9+8], r12
	mov r12, rbp
	xor r12, rcx
	mov QWORD PTR [r9+16], rcx
	mov rcx, r12
	xor rcx, rax
	xor r11, rcx
	mov QWORD PTR [r9+24], r14
	mov r14, rax
	xor r14, r13
	mov QWORD PTR [r9+32], rax
	mov rax, rcx
	xor rax, r10
	mov QWORD PTR [r9+40], r14
	mov r14, rcx
	xor r14, r15
	mov QWORD PTR [r9+48], r14
	mov r14, r11
	xor r14, r13
	mov QWORD PTR [r9+56], r13
	mov r13, rax
	xor r13, r14
	mov QWORD PTR [r9+64], r11
	mov r11, rax
	and r11, rcx
	mov QWORD PTR [r9+72], rcx
	mov rcx, r12
	xor rcx, r10
	xor r10, rbp
	xor rbp, rax
	mov QWORD PTR [r9+80], rax
	mov rax, r14
	and rax, r15
	mov QWORD PTR [r9+88], r15
	mov r15, rcx
	and r15, rbp
	xor rbx, rcx
	xor rax, r15
	mov QWORD PTR [r9+96], rbp
	mov rbp, r13
	and rbp, QWORD PTR [r9+48]
	xor r15, rbp
	mov rbp, QWORD PTR [r9+48]
	xor rbp, rbx
	mov QWORD PTR [r9+104], r13
	mov r13, rcx
	xor r13, QWORD PTR [r9+64]
	mov QWORD PTR [r9+112], rcx
	mov rcx, QWORD PTR [r9+40]
	and rcx, rbx
	mov QWORD PTR [r9+120], rbx
	mov rbx, r13
	and rbx, rbp
	xor rcx, r15
	xor r15, rbx
	mov rbx, QWORD PTR [r9+32]
	and rbx, r10
	mov QWORD PTR [r9+128], rbp
	mov rbp, QWORD PTR [r9+56]
	and rbp, QWORD PTR [r9+24]
	xor rcx, r11
	xor r15, rbx
	xor r11, rbp
	xor rbx, rax
	mov rbp, r14
	xor rbp, QWORD PTR [r9+8]
	xor rcx, QWORD PTR [r9+16]
	xor r11, rax
	mov rax, QWORD PTR [r9+64]
	and rax, QWORD PTR [r9+8]
	xor r11, rbp
	xor rbx, rax
	mov rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9+24]
	xor rbx, rax
	xor r15, r12
	mov r12, rcx
	xor r12, r15
	mov rax, r11
	and rax, rcx
	mov rbp, r15
	xor rbp, rax
	xor rax, rbx
	and rax, r12
	xor r11, rbx
	xor rax, r15
	xor rcx, rax
	mov r12, rax
	and r12, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], r12
	mov r12, rbp
	xor r12, rax
	and r15, r12
	xor rcx, r15
	and r14, rcx
	xor r15, rbp
	and rbp, r11
	xor rbx, rbp
	mov rbp, rcx
	and rbp, QWORD PTR [r9+88]
	and r15, rbx
	xor r15, r11
	mov r11, rbx
	xor r11, r15
	and r13, r11
	mov r12, rbx
	xor r12, rax
	and r10, r12
	and r11, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r14
	mov r14, r15
	and r14, QWORD PTR [r9+104]
	mov QWORD PTR [r9+104], r14
	mov r14, r12
	and r14, QWORD PTR [r9+32]
	xor r14, r13
	mov QWORD PTR [r9+32], r14
	mov r14, r15
	and r14, QWORD PTR [r9+48]
	xor r15, rcx
	xor r12, r15
	xor r13, QWORD PTR [r9+56]
	xor rcx, rax
	and rax, QWORD PTR [r9+24]
	xor r11, r14
	xor r10, r11
	mov QWORD PTR [r9+24], r10
	mov r10, r12
	and r10, QWORD PTR [r9+96]
	xor r11, r10
	xor r11, rax
	xor rbp, rax
	mov rax, rcx
	and rax, QWORD PTR [r9+8]
	and rcx, QWORD PTR [r9+64]
	xor r11, rax
	and r12, QWORD PTR [r9+112]
	mov rax, rbx
	and rax, QWORD PTR [r9+120]
	xor r12, QWORD PTR [r9+104]
	xor r14, rax
	mov rax, r15
	and rax, QWORD PTR [r9+80]
	and rbx, QWORD PTR [r9+40]
	xor rax, r12
	xor r14, rbp
	xor r13, rax
	xor rax, rbx
	xor rax, QWORD PTR [r9]
	and r15, QWORD PTR [r9+72]
	xor r13, rcx
	xor r11, r15
	xor r12, QWORD PTR [r9+32]
	xor r12, r14
	xor r12, QWORD PTR [r9]
	xor r14, rax
	xor r10, rax
	xor r10, QWORD PTR [r9]
	xor rbp, r10
	xor r10, r13
	xor rbx, r12
	xor rbx, QWORD PTR [r9]
	xor rbx, QWORD PTR [r9+128]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9]
	xor rbp, r15
	xor rbx, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], rax
	mov rax, r12
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+56]
	mov rcx, r13
	mov QWORD PTR [r9+24], rbp
	mov rbp, r11
	mov QWORD PTR [r9+128], r10
	mov r10, QWORD PTR [r9+104]
	mov r11, r14
	mov r12, QWORD PTR [r9+128]
	mov r13, QWORD PTR [r9+24]
	mov QWORD PTR [r9+64], rax
	mov QWORD PTR [r9+72], rbx
	mov QWORD PTR [r9+80], rcx
	mov QWORD PTR [r9+88], rbp
	mov QWORD PTR [r9+96], r10
	mov QWORD PTR [r9+104], r11
	mov QWORD PTR [r9+112], r12
	mov QWORD PTR [r9+120], r13
	xor rcx, rbx
	xor rbp, rcx
	xor r10, rax
	xor rax, r12
	xor r12, r13
	xor r12, rbx
	xor rbx, r10
	xor r10, r11
	xor r11, rcx
	xor rcx, r13
	xor r13, rbp
	xor r10, rbp
	xor rax, r10
	xor rcx, rbx
	and rax, QWORD PTR [r9+408]
	mov QWORD PTR [r9+128], rax
	and r11, QWORD PTR [r9+408]
	mov QWORD PTR [r9+136], r11
	and rbp, QWORD PTR [r9+408]
	mov QWORD PTR [r9+144], rbp
	and r13, QWORD PTR [r9+408]
	mov QWORD PTR [r9+152], r13
	and rcx, QWORD PTR [r9+408]
	mov QWORD PTR [r9+160], rcx
	and rbx, QWORD PTR [r9+408]
	mov QWORD PTR [r9+168], rbx
	and r10, QWORD PTR [r9+408]
	mov QWORD PTR [r9+176], r10
	and r12, QWORD PTR [r9+408]
	mov QWORD PTR [r9+184], r12
	mov rax, QWORD PTR [r9+64]
	mov rbx, QWORD PTR [r9+72]
	mov rcx, QWORD PTR [r9+80]
	mov rbp, QWORD PTR [r9+88]
	mov r10, QWORD PTR [r9+96]
	mov r11, QWORD PTR [r9+104]
	mov r12, QWORD PTR [r9+112]
	mov r13, QWORD PTR [r9+120]
	xor r10, r12
	xor rcx, r10
	xor r12, rbp
	xor r10, rax
	xor r12, rbx
	xor rbp, rcx
	xor rbp, rax
	xor rbx, r10
	xor r10, r11
	xor rax, r11
	xor r11, rcx
	xor rcx, r13
	xor r13, r12
	xor r12, rax
	xor rax, rcx
	xor r11, QWORD PTR [r9+128]
	mov r14, r11
	shr r14, 16
	xor r14, r11
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r11
	shr r15, 16
	xor r15, r11
	and r15, QWORD PTR [r9+424]
	xor r11, r15
	ror r15, 48
	xor r11, r15
	xor r11, r14
	xor rcx, QWORD PTR [r9+136]
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rcx
	shr r15, 16
	xor r15, rcx
	and r15, QWORD PTR [r9+424]
	xor rcx, r15
	ror r15, 48
	xor rcx, r15
	xor rcx, r14
	xor rbx, QWORD PTR [r9+144]
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rbx
	shr r15, 8
	xor r15, rbx
	and r15, QWORD PTR [r9+432]
	xor rbx, r15
	ror r15, 56
	xor rbx, r15
	xor rbx, r14
	xor rax, QWORD PTR [r9+152]
	mov r14, rax
	shr r14, 16
	xor r14, rax
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rax
	shr r15, 8
	xor r15, rax
	and r15, QWORD PTR [r9+432]
	xor rax, r15
	ror r15, 56
	xor rax, r15
	xor rax, r14
	xor rbp, QWORD PTR [r9+160]
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rbp
	shr r15, 16
	xor r15, rbp
	and r15, QWORD PTR [r9+416]
	xor rbp, r15
	ror r15, 48
	xor rbp, r15
	xor rbp, r14
	xor r12, QWORD PTR [r9+168]
	mov r14, r12
	shr r14, 16
	xor r14, r12
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r12
	shr r15, 16
	xor r15, r12
	and r15, QWORD PTR [r9+416]
	xor r12, r15
	ror r15, 48
	xor r12, r15
	xor r12, r14
	xor r10, QWORD PTR [r9+176]
	mov r14, r10
	shr r14, 16
	xor r14, r10
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r10
	shr r15, 8
	xor r15, r10
	and r15, QWORD PTR [r9+432]
	xor r10, r15
	ror r15, 56
	xor r10, r15
	mov r15, r10
	shr r15, 16
	xor r15, r10
	and r15, QWORD PTR [r9+440]
	xor r10, r15
	ror r15, 48
	xor r10, r15
	xor r10, r14
	xor r13, QWORD PTR [r9+184]
	mov r14, r13
	shr r14, 16
	xor r14, r13
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r13
	shr r15, 8
	xor r15, r13
	and r15, QWORD PTR [r9+432]
	xor r13, r15
	ror r15, 56
	xor r13, r15
	mov r15, r13
	shr r15, 16
	xor r15, r13
	and r15, QWORD PTR [r9+440]
	xor r13, r15
	ror r15, 48
	xor r13, r15
	xor r13, r14
	mov r14, r11
	shr r14, 4
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	ror r14, 60
	xor r11, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rax
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rax, r14
	mov r14, r11
	shr r14, 2
	xor r14, rbx
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	ror r14, 62
	xor r11, r14
	mov r14, rcx
	shr r14, 2
	xor r14, rax
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	ror r14, 62
	xor rcx, r14
	mov r14, rbp
	shr r14, 2
	xor r14, r10
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	ror r14, 62
	xor rbp, r14
	mov r14, r12
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	ror r14, 62
	xor r12, r14
	mov r14, r11
	shr r14, 1
	xor r14, rcx
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	ror r14, 63
	xor r11, r14
	mov r14, rbx
	shr r14, 1
	xor r14, rax
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	ror r14, 63
	xor rbx, r14
	mov r14, rbp
	shr r14, 1
	xor r14, r12
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	ror r14, 63
	xor rbp, r14
	mov r14, r10
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r10, r14
	xor r11, QWORD PTR [r9+448]
	mov QWORD PTR [r9+488], r11
	xor rcx, QWORD PTR [r9+448]
	mov QWORD PTR [r9+496], rcx
	xor rbx, QWORD PTR [r9+448]
	mov QWORD PTR [r9+504], rbx
	xor rax, QWORD PTR [r9+448]
	mov QWORD PTR [r9+512], rax
	xor rbp, QWORD PTR [r9+448]
	mov QWORD PTR [r9+520], rbp
	xor r12, QWORD PTR [r9+448]
	mov QWORD PTR [r9+528], r12
	xor r10, QWORD PTR [r9+448]
	mov QWORD PTR [r9+536], r10
	xor r13, QWORD PTR [r9+448]
	mov QWORD PTR [r9+544], r13
	mov eax, DWORD PTR [r9+488]
	mov DWORD PTR [r9+616], eax
	add eax, DWORD PTR [r9+552]
	mov DWORD PTR [r9+488], eax
	mov eax, DWORD PTR [r9+492]
	mov DWORD PTR [r9+620], eax
	add eax, DWORD PTR [r9+556]
	mov DWORD PTR [r9+492], eax
	mov eax, DWORD PTR [r9+496]
	mov DWORD PTR [r9+624], eax
	add eax, DWORD PTR [r9+560]
	mov DWORD PTR [r9+496], eax
	mov eax, DWORD PTR [r9+500]
	mov DWORD PTR [r9+628], eax
	add eax, DWORD PTR [r9+564]
	mov DWORD PTR [r9+500], eax
	mov eax, DWORD PTR [r9+504]
	mov DWORD PTR [r9+632], eax
	add eax, DWORD PTR [r9+568]
	mov DWORD PTR [r9+504], eax
	mov eax, DWORD PTR [r9+508]
	mov DWORD PTR [r9+636], eax
	add eax, DWORD PTR [r9+572]
	mov DWORD PTR [r9+508], eax
	mov eax, DWORD PTR [r9+512]
	mov DWORD PTR [r9+640], eax
	add eax, DWORD PTR [r9+576]
	mov DWORD PTR [r9+512], eax
	mov eax, DWORD PTR [r9+516]
	mov DWORD PTR [r9+644], eax
	add eax, DWORD PTR [r9+580]
	mov DWORD PTR [r9+516], eax
	mov eax, DWORD PTR [r9+520]
	mov DWORD PTR [r9+648], eax
	add eax, DWORD PTR [r9+584]
	mov DWORD PTR [r9+520], eax
	mov eax, DWORD PTR [r9+524]
	mov DWORD PTR [r9+652], eax
	add eax, DWORD PTR [r9+588]
	mov DWORD PTR [r9+524], eax
	mov eax, DWORD PTR [r9+528]
	mov DWORD PTR [r9+656], eax
	add eax, DWORD PTR [r9+592]
	mov DWORD PTR [r9+528], eax
	mov eax, DWORD PTR [r9+532]
	mov DWORD PTR [r9+660], eax
	add eax, DWORD PTR [r9+596]
	mov DWORD PTR [r9+532], eax
	mov eax, DWORD PTR [r9+536]
	mov DWORD PTR [r9+664], eax
	add eax, DWORD PTR [r9+600]
	mov DWORD PTR [r9+536], eax
	mov eax, DWORD PTR [r9+540]
	mov DWORD PTR [r9+668], eax
	add eax, DWORD PTR [r9+604]
	mov DWORD PTR [r9+540], eax
	mov eax, DWORD PTR [r9+544]
	mov DWORD PTR [r9+672], eax
	add eax, DWORD PTR [r9+608]
	mov DWORD PTR [r9+544], eax
	mov eax, DWORD PTR [r9+548]
	mov DWORD PTR [r9+676], eax
	add eax, DWORD PTR [r9+612]
	mov DWORD PTR [r9+548], eax
	mov rax, QWORD PTR [r9+488]
	mov rbp, QWORD PTR [r9+496]
	mov r10, QWORD PTR [r9+504]
	mov r12, QWORD PTR [r9+512]
	mov r11, QWORD PTR [r9+520]
	mov r13, QWORD PTR [r9+528]
	mov rbx, QWORD PTR [r9+536]
	mov rcx, QWORD PTR [r9+544]
	mov r14, rax
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, r10
	shr r14, 4
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	ror r14, 60
	xor r10, r14
	mov r14, r12
	shr r14, 4
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	ror r14, 60
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, r10
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbp
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	ror r14, 62
	xor rbp, r14
	mov r14, r11
	shr r14, 2
	xor r14, rbx
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	ror r14, 62
	xor r11, r14
	mov r14, r13
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	ror r14, 62
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	ror r14, 63
	xor rax, r14
	mov r14, r10
	shr r14, 1
	xor r14, r12
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	ror r14, 63
	xor r10, r14
	mov r14, r11
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r11, r14
	mov r14, rbx
	shr r14, 1
	xor r14, rcx
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	ror r14, 63
	xor rbx, r14
	xor r13, r11
	xor rcx, r13
	xor rax, r12
	xor rax, rbp
	xor rbp, r11
	xor r11, r12
	xor r12, r13
	xor r13, rbx
	xor rbx, rcx
	xor r12, r10
	xor rbx, r12
	xor r10, rbp
	xor rbp, r12
	movabs r14, -1
	mov QWORD PTR [r9], r14
	xor rcx, r11
	mov r14, rcx
	xor r14, rbx
	mov r15, r14
	xor r15, r12
	xor rax, r14
	xor rbp, r15
	xor rbp, r13
	mov QWORD PTR [r9+8], r12
	mov r12, rbp
	xor r12, rcx
	mov QWORD PTR [r9+16], rcx
	mov rcx, r12
	xor rcx, rax
	xor r11, rcx
	mov QWORD PTR [r9+24], r14
	mov r14, rax
	xor r14, r13
	mov QWORD PTR [r9+32], rax
	mov rax, rcx
	xor rax, r10
	mov QWORD PTR [r9+40], r14
	mov r14, rcx
	xor r14, r15
	mov QWORD PTR [r9+48], r14
	mov r14, r11
	xor r14, r13
	mov QWORD PTR [r9+56], r13
	mov r13, rax
	xor r13, r14
	mov QWORD PTR [r9+64], r11
	mov r11, rax
	and r11, rcx
	mov QWORD PTR [r9+72], rcx
	mov rcx, r12
	xor rcx, r10
	xor r10, rbp
	xor rbp, rax
	mov QWORD PTR [r9+80], rax
	mov rax, r14
	and rax, r15
	mov QWORD PTR [r9+88], r15
	mov r15, rcx
	and r15, rbp
	xor rbx, rcx
	xor rax, r15
	mov QWORD PTR [r9+96], rbp
	mov rbp, r13
	and rbp, QWORD PTR [r9+48]
	xor r15, rbp
	mov rbp, QWORD PTR [r9+48]
	xor rbp, rbx
	mov QWORD PTR [r9+104], r13
	mov r13, rcx
	xor r13, QWORD PTR [r9+64]
	mov QWORD PTR [r9+112], rcx
	mov rcx, QWORD PTR [r9+40]
	and rcx, rbx
	mov QWORD PTR [r9+120], rbx
	mov rbx, r13
	and rbx, rbp
	xor rcx, r15
	xor r15, rbx
	mov rbx, QWORD PTR [r9+32]
	and rbx, r10
	mov QWORD PTR [r9+128], rbp
	mov rbp, QWORD PTR [r9+56]
	and rbp, QWORD PTR [r9+24]
	xor rcx, r11
	xor r15, rbx
	xor r11, rbp
	xor rbx, rax
	mov rbp, r14
	xor rbp, QWORD PTR [r9+8]
	xor rcx, QWORD PTR [r9+16]
	xor r11, rax
	mov rax, QWORD PTR [r9+64]
	and rax, QWORD PTR [r9+8]
	xor r11, rbp
	xor rbx, rax
	mov rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9+24]
	xor rbx, rax
	xor r15, r12
	mov r12, rcx
	xor r12, r15
	mov rax, r11
	and rax, rcx
	mov rbp, r15
	xor rbp, rax
	xor rax, rbx
	and rax, r12
	xor r11, rbx
	xor rax, r15
	xor rcx, rax
	mov r12, rax
	and r12, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], r12
	mov r12, rbp
	xor r12, rax
	and r15, r12
	xor rcx, r15
	and r14, rcx
	xor r15, rbp
	and rbp, r11
	xor rbx, rbp
	mov rbp, rcx
	and rbp, QWORD PTR [r9+88]
	and r15, rbx
	xor r15, r11
	mov r11, rbx
	xor r11, r15
	and r13, r11
	mov r12, rbx
	xor r12, rax
	and r10, r12
	and r11, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r14
	mov r14, r15
	and r14, QWORD PTR [r9+104]
	mov QWORD PTR [r9+104], r14
	mov r14, r12
	and r14, QWORD PTR [r9+32]
	xor r14, r13
	mov QWORD PTR [r9+32], r14
	mov r14, r15
	and r14, QWORD PTR [r9+48]
	xor r15, rcx
	xor r12, r15
	xor r13, QWORD PTR [r9+56]
	xor rcx, rax
	and rax, QWORD PTR [r9+24]
	xor r11, r14
	xor r10, r11
	mov QWORD PTR [r9+24], r10
	mov r10, r12
	and r10, QWORD PTR [r9+96]
	xor r11, r10
	xor r11, rax
	xor rbp, rax
	mov rax, rcx
	and rax, QWORD PTR [r9+8]
	and rcx, QWORD PTR [r9+64]
	xor r11, rax
	and r12, QWORD PTR [r9+112]
	mov rax, rbx
	and rax, QWORD PTR [r9+120]
	xor r12, QWORD PTR [r9+104]
	xor r14, rax
	mov rax, r15
	and rax, QWORD PTR [r9+80]
	and rbx, QWORD PTR [r9+40]
	xor rax, r12
	xor r14, rbp
	xor r13, rax
	xor rax, rbx
	xor rax, QWORD PTR [r9]
	and r15, QWORD PTR [r9+72]
	xor r13, rcx
	xor r11, r15
	xor r12, QWORD PTR [r9+32]
	xor r12, r14
	xor r12, QWORD PTR [r9]
	xor r14, rax
	xor r10, rax
	xor r10, QWORD PTR [r9]
	xor rbp, r10
	xor r10, r13
	xor rbx, r12
	xor rbx, QWORD PTR [r9]
	xor rbx, QWORD PTR [r9+128]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9]
	xor rbp, r15
	xor rbx, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], rax
	mov rax, r12
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+56]
	mov rcx, r13
	mov QWORD PTR [r9+24], rbp
	mov rbp, r11
	mov QWORD PTR [r9+128], r10
	mov r10, QWORD PTR [r9+104]
	mov r11, r14
	mov r12, QWORD PTR [r9+128]
	mov r13, QWORD PTR [r9+24]
	mov QWORD PTR [r9+64], rax
	mov QWORD PTR [r9+72], rbx
	mov QWORD PTR [r9+80], rcx
	mov QWORD PTR [r9+88], rbp
	mov QWORD PTR [r9+96], r10
	mov QWORD PTR [r9+104], r11
	mov QWORD PTR [r9+112], r12
	mov QWORD PTR [r9+120], r13
	xor rcx, rbx
	xor rbp, rcx
	xor r10, rax
	xor rax, r12
	xor r12, r13
	xor r12, rbx
	xor rbx, r10
	xor r10, r11
	xor r11, rcx
	xor rcx, r13
	xor r13, rbp
	xor r10, rbp
	xor rax, r10
	xor rcx, rbx
	and rax, QWORD PTR [r9+408]
	mov QWORD PTR [r9+128], rax
	and r11, QWORD PTR [r9+408]
	mov QWORD PTR [r9+136], r11
	and rbp, QWORD PTR [r9+408]
	mov QWORD PTR [r9+144], rbp
	and r13, QWORD PTR [r9+408]
	mov QWORD PTR [r9+152], r13
	and rcx, QWORD PTR [r9+408]
	mov QWORD PTR [r9+160], rcx
	and rbx, QWORD PTR [r9+408]
	mov QWORD PTR [r9+168], rbx
	and r10, QWORD PTR [r9+408]
	mov QWORD PTR [r9+176], r10
	and r12, QWORD PTR [r9+408]
	mov QWORD PTR [r9+184], r12
	mov rax, QWORD PTR [r9+64]
	mov rbx, QWORD PTR [r9+72]
	mov rcx, QWORD PTR [r9+80]
	mov rbp, QWORD PTR [r9+88]
	mov r10, QWORD PTR [r9+96]
	mov r11, QWORD PTR [r9+104]
	mov r12, QWORD PTR [r9+112]
	mov r13, QWORD PTR [r9+120]
	xor r10, r12
	xor rcx, r10
	xor r12, rbp
	xor r10, rax
	xor r12, rbx
	xor rbp, rcx
	xor rbp, rax
	xor rbx, r10
	xor r10, r11
	xor rax, r11
	xor r11, rcx
	xor rcx, r13
	xor r13, r12
	xor r12, rax
	xor rax, rcx
	xor r11, QWORD PTR [r9+128]
	mov r14, r11
	shr r14, 16
	xor r14, r11
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r11
	shr r15, 16
	xor r15, r11
	and r15, QWORD PTR [r9+424]
	xor r11, r15
	ror r15, 48
	xor r11, r15
	xor r11, r14
	xor rcx, QWORD PTR [r9+136]
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rcx
	shr r15, 16
	xor r15, rcx
	and r15, QWORD PTR [r9+424]
	xor rcx, r15
	ror r15, 48
	xor rcx, r15
	xor rcx, r14
	xor rbx, QWORD PTR [r9+144]
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rbx
	shr r15, 8
	xor r15, rbx
	and r15, QWORD PTR [r9+432]
	xor rbx, r15
	ror r15, 56
	xor rbx, r15
	xor rbx, r14
	xor rax, QWORD PTR [r9+152]
	mov r14, rax
	shr r14, 16
	xor r14, rax
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rax
	shr r15, 8
	xor r15, rax
	and r15, QWORD PTR [r9+432]
	xor rax, r15
	ror r15, 56
	xor rax, r15
	xor rax, r14
	xor rbp, QWORD PTR [r9+160]
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rbp
	shr r15, 16
	xor r15, rbp
	and r15, QWORD PTR [r9+416]
	xor rbp, r15
	ror r15, 48
	xor rbp, r15
	xor rbp, r14
	xor r12, QWORD PTR [r9+168]
	mov r14, r12
	shr r14, 16
	xor r14, r12
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r12
	shr r15, 16
	xor r15, r12
	and r15, QWORD PTR [r9+416]
	xor r12, r15
	ror r15, 48
	xor r12, r15
	xor r12, r14
	xor r10, QWORD PTR [r9+176]
	mov r14, r10
	shr r14, 16
	xor r14, r10
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r10
	shr r15, 8
	xor r15, r10
	and r15, QWORD PTR [r9+432]
	xor r10, r15
	ror r15, 56
	xor r10, r15
	mov r15, r10
	shr r15, 16
	xor r15, r10
	and r15, QWORD PTR [r9+440]
	xor r10, r15
	ror r15, 48
	xor r10, r15
	xor r10, r14
	xor r13, QWORD PTR [r9+184]
	mov r14, r13
	shr r14, 16
	xor r14, r13
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r13
	shr r15, 8
	xor r15, r13
	and r15, QWORD PTR [r9+432]
	xor r13, r15
	ror r15, 56
	xor r13, r15
	mov r15, r13
	shr r15, 16
	xor r15, r13
	and r15, QWORD PTR [r9+440]
	xor r13, r15
	ror r15, 48
	xor r13, r15
	xor r13, r14
	mov r14, r11
	shr r14, 4
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	ror r14, 60
	xor r11, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rax
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rax, r14
	mov r14, r11
	shr r14, 2
	xor r14, rbx
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	ror r14, 62
	xor r11, r14
	mov r14, rcx
	shr r14, 2
	xor r14, rax
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	ror r14, 62
	xor rcx, r14
	mov r14, rbp
	shr r14, 2
	xor r14, r10
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	ror r14, 62
	xor rbp, r14
	mov r14, r12
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	ror r14, 62
	xor r12, r14
	mov r14, r11
	shr r14, 1
	xor r14, rcx
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	ror r14, 63
	xor r11, r14
	mov r14, rbx
	shr r14, 1
	xor r14, rax
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	ror r14, 63
	xor rbx, r14
	mov r14, rbp
	shr r14, 1
	xor r14, r12
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	ror r14, 63
	xor rbp, r14
	mov r14, r10
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r10, r14
	xor r11, QWORD PTR [r9+448]
	mov QWORD PTR [r9+488], r11
	xor rcx, QWORD PTR [r9+448]
	mov QWORD PTR [r9+496], rcx
	xor rbx, QWORD PTR [r9+448]
	mov QWORD PTR [r9+504], rbx
	xor rax, QWORD PTR [r9+448]
	mov QWORD PTR [r9+512], rax
	xor rbp, QWORD PTR [r9+448]
	mov QWORD PTR [r9+520], rbp
	xor r12, QWORD PTR [r9+448]
	mov QWORD PTR [r9+528], r12
	xor r10, QWORD PTR [r9+448]
	mov QWORD PTR [r9+536], r10
	xor r13, QWORD PTR [r9+448]
	mov QWORD PTR [r9+544], r13
	mov eax, DWORD PTR [r9+488]
	mov DWORD PTR [r9+680], eax
	add eax, DWORD PTR [r9+616]
	mov DWORD PTR [r9+488], eax
	mov eax, DWORD PTR [r9+492]
	mov DWORD PTR [r9+684], eax
	add eax, DWORD PTR [r9+620]
	mov DWORD PTR [r9+492], eax
	mov eax, DWORD PTR [r9+496]
	mov DWORD PTR [r9+688], eax
	add eax, DWORD PTR [r9+624]
	mov DWORD PTR [r9+496], eax
	mov eax, DWORD PTR [r9+500]
	mov DWORD PTR [r9+692], eax
	add eax, DWORD PTR [r9+628]
	mov DWORD PTR [r9+500], eax
	mov eax, DWORD PTR [r9+504]
	mov DWORD PTR [r9+696], eax
	add eax, DWORD PTR [r9+632]
	mov DWORD PTR [r9+504], eax
	mov eax, DWORD PTR [r9+508]
	mov DWORD PTR [r9+700], eax
	add eax, DWORD PTR [r9+636]
	mov DWORD PTR [r9+508], eax
	mov eax, DWORD PTR [r9+512]
	mov DWORD PTR [r9+704], eax
	add eax, DWORD PTR [r9+640]
	mov DWORD PTR [r9+512], eax
	mov eax, DWORD PTR [r9+516]
	mov DWORD PTR [r9+708], eax
	add eax, DWORD PTR [r9+644]
	mov DWORD PTR [r9+516], eax
	mov eax, DWORD PTR [r9+520]
	mov DWORD PTR [r9+712], eax
	add eax, DWORD PTR [r9+648]
	mov DWORD PTR [r9+520], eax
	mov eax, DWORD PTR [r9+524]
	mov DWORD PTR [r9+716], eax
	add eax, DWORD PTR [r9+652]
	mov DWORD PTR [r9+524], eax
	mov eax, DWORD PTR [r9+528]
	mov DWORD PTR [r9+720], eax
	add eax, DWORD PTR [r9+656]
	mov DWORD PTR [r9+528], eax
	mov eax, DWORD PTR [r9+532]
	mov DWORD PTR [r9+724], eax
	add eax, DWORD PTR [r9+660]
	mov DWORD PTR [r9+532], eax
	mov eax, DWORD PTR [r9+536]
	mov DWORD PTR [r9+728], eax
	add eax, DWORD PTR [r9+664]
	mov DWORD PTR [r9+536], eax
	mov eax, DWORD PTR [r9+540]
	mov DWORD PTR [r9+732], eax
	add eax, DWORD PTR [r9+668]
	mov DWORD PTR [r9+540], eax
	mov eax, DWORD PTR [r9+544]
	mov DWORD PTR [r9+736], eax
	add eax, DWORD PTR [r9+672]
	mov DWORD PTR [r9+544], eax
	mov eax, DWORD PTR [r9+548]
	mov DWORD PTR [r9+740], eax
	add eax, DWORD PTR [r9+676]
	mov DWORD PTR [r9+548], eax
	mov rax, QWORD PTR [r9+488]
	mov rbp, QWORD PTR [r9+496]
	mov r10, QWORD PTR [r9+504]
	mov r12, QWORD PTR [r9+512]
	mov r11, QWORD PTR [r9+520]
	mov r13, QWORD PTR [r9+528]
	mov rbx, QWORD PTR [r9+536]
	mov rcx, QWORD PTR [r9+544]
	mov r14, rax
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, r10
	shr r14, 4
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	ror r14, 60
	xor r10, r14
	mov r14, r12
	shr r14, 4
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	ror r14, 60
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, r10
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbp
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	ror r14, 62
	xor rbp, r14
	mov r14, r11
	shr r14, 2
	xor r14, rbx
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	ror r14, 62
	xor r11, r14
	mov r14, r13
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	ror r14, 62
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	ror r14, 63
	xor rax, r14
	mov r14, r10
	shr r14, 1
	xor r14, r12
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	ror r14, 63
	xor r10, r14
	mov r14, r11
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r11, r14
	mov r14, rbx
	shr r14, 1
	xor r14, rcx
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	ror r14, 63
	xor rbx, r14
	xor r13, r11
	xor rcx, r13
	xor rax, r12
	xor rax, rbp
	xor rbp, r11
	xor r11, r12
	xor r12, r13
	xor r13, rbx
	xor rbx, rcx
	xor r12, r10
	xor rbx, r12
	xor r10, rbp
	xor rbp, r12
	movabs r14, -1
	mov QWORD PTR [r9], r14
	xor rcx, r11
	mov r14, rcx
	xor r14, rbx
	mov r15, r14
	xor r15, r12
	xor rax, r14
	xor rbp, r15
	xor rbp, r13
	mov QWORD PTR [r9+8], r12
	mov r12, rbp
	xor r12, rcx
	mov QWORD PTR [r9+16], rcx
	mov rcx, r12
	xor rcx, rax
	xor r11, rcx
	mov QWORD PTR [r9+24], r14
	mov r14, rax
	xor r14, r13
	mov QWORD PTR [r9+32], rax
	mov rax, rcx
	xor rax, r10
	mov QWORD PTR [r9+40], r14
	mov r14, rcx
	xor r14, r15
	mov QWORD PTR [r9+48], r14
	mov r14, r11
	xor r14, r13
	mov QWORD PTR [r9+56], r13
	mov r13, rax
	xor r13, r14
	mov QWORD PTR [r9+64], r11
	mov r11, rax
	and r11, rcx
	mov QWORD PTR [r9+72], rcx
	mov rcx, r12
	xor rcx, r10
	xor r10, rbp
	xor rbp, rax
	mov QWORD PTR [r9+80], rax
	mov rax, r14
	and rax, r15
	mov QWORD PTR [r9+88], r15
	mov r15, rcx
	and r15, rbp
	xor rbx, rcx
	xor rax, r15
	mov QWORD PTR [r9+96], rbp
	mov rbp, r13
	and rbp, QWORD PTR [r9+48]
	xor r15, rbp
	mov rbp, QWORD PTR [r9+48]
	xor rbp, rbx
	mov QWORD PTR [r9+104], r13
	mov r13, rcx
	xor r13, QWORD PTR [r9+64]
	mov QWORD PTR [r9+112], rcx
	mov rcx, QWORD PTR [r9+40]
	and rcx, rbx
	mov QWORD PTR [r9+120], rbx
	mov rbx, r13
	and rbx, rbp
	xor rcx, r15
	xor r15, rbx
	mov rbx, QWORD PTR [r9+32]
	and rbx, r10
	mov QWORD PTR [r9+128], rbp
	mov rbp, QWORD PTR [r9+56]
	and rbp, QWORD PTR [r9+24]
	xor rcx, r11
	xor r15, rbx
	xor r11, rbp
	xor rbx, rax
	mov rbp, r14
	xor rbp, QWORD PTR [r9+8]
	xor rcx, QWORD PTR [r9+16]
	xor r11, rax
	mov rax, QWORD PTR [r9+64]
	and rax, QWORD PTR [r9+8]
	xor r11, rbp
	xor rbx, rax
	mov rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9+24]
	xor rbx, rax
	xor r15, r12
	mov r12, rcx
	xor r12, r15
	mov rax, r11
	and rax, rcx
	mov rbp, r15
	xor rbp, rax
	xor rax, rbx
	and rax, r12
	xor r11, rbx
	xor rax, r15
	xor rcx, rax
	mov r12, rax
	and r12, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], r12
	mov r12, rbp
	xor r12, rax
	and r15, r12
	xor rcx, r15
	and r14, rcx
	xor r15, rbp
	and rbp, r11
	xor rbx, rbp
	mov rbp, rcx
	and rbp, QWORD PTR [r9+88]
	and r15, rbx
	xor r15, r11
	mov r11, rbx
	xor r11, r15
	and r13, r11
	mov r12, rbx
	xor r12, rax
	and r10, r12
	and r11, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r14
	mov r14, r15
	and r14, QWORD PTR [r9+104]
	mov QWORD PTR [r9+104], r14
	mov r14, r12
	and r14, QWORD PTR [r9+32]
	xor r14, r13
	mov QWORD PTR [r9+32], r14
	mov r14, r15
	and r14, QWORD PTR [r9+48]
	xor r15, rcx
	xor r12, r15
	xor r13, QWORD PTR [r9+56]
	xor rcx, rax
	and rax, QWORD PTR [r9+24]
	xor r11, r14
	xor r10, r11
	mov QWORD PTR [r9+24], r10
	mov r10, r12
	and r10, QWORD PTR [r9+96]
	xor r11, r10
	xor r11, rax
	xor rbp, rax
	mov rax, rcx
	and rax, QWORD PTR [r9+8]
	and rcx, QWORD PTR [r9+64]
	xor r11, rax
	and r12, QWORD PTR [r9+112]
	mov rax, rbx
	and rax, QWORD PTR [r9+120]
	xor r12, QWORD PTR [r9+104]
	xor r14, rax
	mov rax, r15
	and rax, QWORD PTR [r9+80]
	and rbx, QWORD PTR [r9+40]
	xor rax, r12
	xor r14, rbp
	xor r13, rax
	xor rax, rbx
	xor rax, QWORD PTR [r9]
	and r15, QWORD PTR [r9+72]
	xor r13, rcx
	xor r11, r15
	xor r12, QWORD PTR [r9+32]
	xor r12, r14
	xor r12, QWORD PTR [r9]
	xor r14, rax
	xor r10, rax
	xor r10, QWORD PTR [r9]
	xor rbp, r10
	xor r10, r13
	xor rbx, r12
	xor rbx, QWORD PTR [r9]
	xor rbx, QWORD PTR [r9+128]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9]
	xor rbp, r15
	xor rbx, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], rax
	mov rax, r12
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+56]
	mov rcx, r13
	mov QWORD PTR [r9+24], rbp
	mov rbp, r11
	mov QWORD PTR [r9+128], r10
	mov r10, QWORD PTR [r9+104]
	mov r11, r14
	mov r12, QWORD PTR [r9+128]
	mov r13, QWORD PTR [r9+24]
	mov QWORD PTR [r9+64], rax
	mov QWORD PTR [r9+72], rbx
	mov QWORD PTR [r9+80], rcx
	mov QWORD PTR [r9+88], rbp
	mov QWORD PTR [r9+96], r10
	mov QWORD PTR [r9+104], r11
	mov QWORD PTR [r9+112], r12
	mov QWORD PTR [r9+120], r13
	xor rcx, rbx
	xor rbp, rcx
	xor r10, rax
	xor rax, r12
	xor r12, r13
	xor r12, rbx
	xor rbx, r10
	xor r10, r11
	xor r11, rcx
	xor rcx, r13
	xor r13, rbp
	xor r10, rbp
	xor rax, r10
	xor rcx, rbx
	and rax, QWORD PTR [r9+408]
	mov QWORD PTR [r9+128], rax
	and r11, QWORD PTR [r9+408]
	mov QWORD PTR [r9+136], r11
	and rbp, QWORD PTR [r9+408]
	mov QWORD PTR [r9+144], rbp
	and r13, QWORD PTR [r9+408]
	mov QWORD PTR [r9+152], r13
	and rcx, QWORD PTR [r9+408]
	mov QWORD PTR [r9+160], rcx
	and rbx, QWORD PTR [r9+408]
	mov QWORD PTR [r9+168], rbx
	and r10, QWORD PTR [r9+408]
	mov QWORD PTR [r9+176], r10
	and r12, QWORD PTR [r9+408]
	mov QWORD PTR [r9+184], r12
	mov rax, QWORD PTR [r9+64]
	mov rbx, QWORD PTR [r9+72]
	mov rcx, QWORD PTR [r9+80]
	mov rbp, QWORD PTR [r9+88]
	mov r10, QWORD PTR [r9+96]
	mov r11, QWORD PTR [r9+104]
	mov r12, QWORD PTR [r9+112]
	mov r13, QWORD PTR [r9+120]
	xor r10, r12
	xor rcx, r10
	xor r12, rbp
	xor r10, rax
	xor r12, rbx
	xor rbp, rcx
	xor rbp, rax
	xor rbx, r10
	xor r10, r11
	xor rax, r11
	xor r11, rcx
	xor rcx, r13
	xor r13, r12
	xor r12, rax
	xor rax, rcx
	xor r11, QWORD PTR [r9+128]
	mov r14, r11
	shr r14, 16
	xor r14, r11
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r11
	shr r15, 16
	xor r15, r11
	and r15, QWORD PTR [r9+424]
	xor r11, r15
	ror r15, 48
	xor r11, r15
	xor r11, r14
	xor rcx, QWORD PTR [r9+136]
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rcx
	shr r15, 16
	xor r15, rcx
	and r15, QWORD PTR [r9+424]
	xor rcx, r15
	ror r15, 48
	xor rcx, r15
	xor rcx, r14
	xor rbx, QWORD PTR [r9+144]
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rbx
	shr r15, 8
	xor r15, rbx
	and r15, QWORD PTR [r9+432]
	xor rbx, r15
	ror r15, 56
	xor rbx, r15
	xor rbx, r14
	xor rax, QWORD PTR [r9+152]
	mov r14, rax
	shr r14, 16
	xor r14, rax
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rax
	shr r15, 8
	xor r15, rax
	and r15, QWORD PTR [r9+432]
	xor rax, r15
	ror r15, 56
	xor rax, r15
	xor rax, r14
	xor rbp, QWORD PTR [r9+160]
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, rbp
	shr r15, 16
	xor r15, rbp
	and r15, QWORD PTR [r9+416]
	xor rbp, r15
	ror r15, 48
	xor rbp, r15
	xor rbp, r14
	xor r12, QWORD PTR [r9+168]
	mov r14, r12
	shr r14, 16
	xor r14, r12
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r12
	shr r15, 16
	xor r15, r12
	and r15, QWORD PTR [r9+416]
	xor r12, r15
	ror r15, 48
	xor r12, r15
	xor r12, r14
	xor r10, QWORD PTR [r9+176]
	mov r14, r10
	shr r14, 16
	xor r14, r10
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r10
	shr r15, 8
	xor r15, r10
	and r15, QWORD PTR [r9+432]
	xor r10, r15
	ror r15, 56
	xor r10, r15
	mov r15, r10
	shr r15, 16
	xor r15, r10
	and r15, QWORD PTR [r9+440]
	xor r10, r15
	ror r15, 48
	xor r10, r15
	xor r10, r14
	xor r13, QWORD PTR [r9+184]
	mov r14, r13
	shr r14, 16
	xor r14, r13
	mov r15, r14
	shr r15, 8
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	mov r15, r14
	ror r15, 56
	xor r14, r15
	mov r15, r14
	ror r15, 48
	xor r14, r15
	mov r15, r13
	shr r15, 8
	xor r15, r13
	and r15, QWORD PTR [r9+432]
	xor r13, r15
	ror r15, 56
	xor r13, r15
	mov r15, r13
	shr r15, 16
	xor r15, r13
	and r15, QWORD PTR [r9+440]
	xor r13, r15
	ror r15, 48
	xor r13, r15
	xor r13, r14
	mov r14, r11
	shr r14, 4
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	ror r14, 60
	xor r11, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rax
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rax, r14
	mov r14, r11
	shr r14, 2
	xor r14, rbx
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	ror r14, 62
	xor r11, r14
	mov r14, rcx
	shr r14, 2
	xor r14, rax
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	ror r14, 62
	xor rcx, r14
	mov r14, rbp
	shr r14, 2
	xor r14, r10
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	ror r14, 62
	xor rbp, r14
	mov r14, r12
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	ror r14, 62
	xor r12, r14
	mov r14, r11
	shr r14, 1
	xor r14, rcx
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	ror r14, 63
	xor r11, r14
	mov r14, rbx
	shr r14, 1
	xor r14, rax
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	ror r14, 63
	xor rbx, r14
	mov r14, rbp
	shr r14, 1
	xor r14, r12
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	ror r14, 63
	xor rbp, r14
	mov r14, r10
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r10, r14
	xor r11, QWORD PTR [r9+448]
	mov QWORD PTR [r9+488], r11
	xor rcx, QWORD PTR [r9+448]
	mov QWORD PTR [r9+496], rcx
	xor rbx, QWORD PTR [r9+448]
	mov QWORD PTR [r9+504], rbx
	xor rax, QWORD PTR [r9+448]
	mov QWORD PTR [r9+512], rax
	xor rbp, QWORD PTR [r9+448]
	mov QWORD PTR [r9+520], rbp
	xor r12, QWORD PTR [r9+448]
	mov QWORD PTR [r9+528], r12
	xor r10, QWORD PTR [r9+448]
	mov QWORD PTR [r9+536], r10
	xor r13, QWORD PTR [r9+448]
	mov QWORD PTR [r9+544], r13
	mov eax, DWORD PTR [r9+488]
	mov ecx, DWORD PTR [r9+808]
	xor ecx, eax
	mov DWORD PTR [r9+808], ecx
	add eax, DWORD PTR [r9+680]
	xor eax, DWORD PTR [r9+744]
	mov DWORD PTR [r9+744], eax
	mov eax, DWORD PTR [r9+492]
	mov ecx, DWORD PTR [r9+812]
	xor ecx, eax
	mov DWORD PTR [r9+812], ecx
	add eax, DWORD PTR [r9+684]
	xor eax, DWORD PTR [r9+748]
	mov DWORD PTR [r9+748], eax
	mov eax, DWORD PTR [r9+496]
	mov ecx, DWORD PTR [r9+816]
	xor ecx, eax
	mov DWORD PTR [r9+816], ecx
	add eax, DWORD PTR [r9+688]
	xor eax, DWORD PTR [r9+752]
	mov DWORD PTR [r9+752], eax
	mov eax, DWORD PTR [r9+500]
	mov ecx, DWORD PTR [r9+820]
	xor ecx, eax
	mov DWORD PTR [r9+820], ecx
	add eax, DWORD PTR [r9+692]
	xor eax, DWORD PTR [r9+756]
	mov DWORD PTR [r9+756], eax
	mov eax, DWORD PTR [r9+504]
	mov ecx, DWORD PTR [r9+824]
	xor ecx, eax
	mov DWORD PTR [r9+824], ecx
	add eax, DWORD PTR [r9+696]
	xor eax, DWORD PTR [r9+760]
	mov DWORD PTR [r9+760], eax
	mov eax, DWORD PTR [r9+508]
	mov ecx, DWORD PTR [r9+828]
	xor ecx, eax
	mov DWORD PTR [r9+828], ecx
	add eax, DWORD PTR [r9+700]
	xor eax, DWORD PTR [r9+764]
	mov DWORD PTR [r9+764], eax
	mov eax, DWORD PTR [r9+512]
	mov ecx, DWORD PTR [r9+832]
	xor ecx, eax
	mov DWORD PTR [r9+832], ecx
	add eax, DWORD PTR [r9+704]
	xor eax, DWORD PTR [r9+768]
	mov DWORD PTR [r9+768], eax
	mov eax, DWORD PTR [r9+516]
	mov ecx, DWORD PTR [r9+836]
	xor ecx, eax
	mov DWORD PTR [r9+836], ecx
	add eax, DWORD PTR [r9+708]
	xor eax, DWORD PTR [r9+772]
	mov DWORD PTR [r9+772], eax
	mov eax, DWORD PTR [r9+520]
	mov ecx, DWORD PTR [r9+840]
	xor ecx, eax
	mov DWORD PTR [r9+840], ecx
	add eax, DWORD PTR [r9+712]
	xor eax, DWORD PTR [r9+776]
	mov DWORD PTR [r9+776], eax
	mov eax, DWORD PTR [r9+524]
	mov ecx, DWORD PTR [r9+844]
	xor ecx, eax
	mov DWORD PTR [r9+844], ecx
	add eax, DWORD PTR [r9+716]
	xor eax, DWORD PTR [r9+780]
	mov DWORD PTR [r9+780], eax
	mov eax, DWORD PTR [r9+528]
	mov ecx, DWORD PTR [r9+848]
	xor ecx, eax
	mov DWORD PTR [r9+848], ecx
	add eax, DWORD PTR [r9+720]
	xor eax, DWORD PTR [r9+784]
	mov DWORD PTR [r9+784], eax
	mov eax, DWORD PTR [r9+532]
	mov ecx, DWORD PTR [r9+852]
	xor ecx, eax
	mov DWORD PTR [r9+852], ecx
	add eax, DWORD PTR [r9+724]
	xor eax, DWORD PTR [r9+788]
	mov DWORD PTR [r9+788], eax
	mov eax, DWORD PTR [r9+536]
	mov ecx, DWORD PTR [r9+856]
	xor ecx, eax
	mov DWORD PTR [r9+856], ecx
	add eax, DWORD PTR [r9+728]
	xor eax, DWORD PTR [r9+792]
	mov DWORD PTR [r9+792], eax
	mov eax, DWORD PTR [r9+540]
	mov ecx, DWORD PTR [r9+860]
	xor ecx, eax
	mov DWORD PTR [r9+860], ecx
	add eax, DWORD PTR [r9+732]
	xor eax, DWORD PTR [r9+796]
	mov DWORD PTR [r9+796], eax
	mov eax, DWORD PTR [r9+544]
	mov ecx, DWORD PTR [r9+864]
	xor ecx, eax
	mov DWORD PTR [r9+864], ecx
	add eax, DWORD PTR [r9+736]
	xor eax, DWORD PTR [r9+800]
	mov DWORD PTR [r9+800], eax
	mov eax, DWORD PTR [r9+548]
	mov ecx, DWORD PTR [r9+868]
	xor ecx, eax
	mov DWORD PTR [r9+868], ecx
	add eax, DWORD PTR [r9+740]
	xor eax, DWORD PTR [r9+804]
	mov DWORD PTR [r9+804], eax
	mov rax, QWORD PTR [r9+744]
	mov rcx, QWORD PTR [r9+872]
	mov QWORD PTR [r9+744], rcx
	mov QWORD PTR [r9+872], rax
	mov rax, QWORD PTR [r9+752]
	mov rcx, QWORD PTR [r9+880]
	mov QWORD PTR [r9+752], rcx
	mov QWORD PTR [r9+880], rax
	mov rax, QWORD PTR [r9+760]
	mov rcx, QWORD PTR [r9+888]
	mov QWORD PTR [r9+760], rcx
	mov QWORD PTR [r9+888], rax
	mov rax, QWORD PTR [r9+768]
	mov rcx, QWORD PTR [r9+896]
	mov QWORD PTR [r9+768], rcx
	mov QWORD PTR [r9+896], rax
	mov rax, QWORD PTR [r9+776]
	mov rcx, QWORD PTR [r9+904]
	mov QWORD PTR [r9+776], rcx
	mov QWORD PTR [r9+904], rax
	mov rax, QWORD PTR [r9+784]
	mov rcx, QWORD PTR [r9+912]
	mov QWORD PTR [r9+784], rcx
	mov QWORD PTR [r9+912], rax
	mov rax, QWORD PTR [r9+792]
	mov rcx, QWORD PTR [r9+920]
	mov QWORD PTR [r9+792], rcx
	mov QWORD PTR [r9+920], rax
	mov rax, QWORD PTR [r9+800]
	mov rcx, QWORD PTR [r9+928]
	mov QWORD PTR [r9+800], rcx
	mov QWORD PTR [r9+928], rax
	mov rax, QWORD PTR [r9+808]
	mov rcx, QWORD PTR [r9+936]
	mov QWORD PTR [r9+808], rcx
	mov QWORD PTR [r9+936], rax
	mov rax, QWORD PTR [r9+816]
	mov rcx, QWORD PTR [r9+944]
	mov QWORD PTR [r9+816], rcx
	mov QWORD PTR [r9+944], rax
	mov rax, QWORD PTR [r9+824]
	mov rcx, QWORD PTR [r9+952]
	mov QWORD PTR [r9+824], rcx
	mov QWORD PTR [r9+952], rax
	mov rax, QWORD PTR [r9+832]
	mov rcx, QWORD PTR [r9+960]
	mov QWORD PTR [r9+832], rcx
	mov QWORD PTR [r9+960], rax
	mov rax, QWORD PTR [r9+840]
	mov rcx, QWORD PTR [r9+968]
	mov QWORD PTR [r9+840], rcx
	mov QWORD PTR [r9+968], rax
	mov rax, QWORD PTR [r9+848]
	mov rcx, QWORD PTR [r9+976]
	mov QWORD PTR [r9+848], rcx
	mov QWORD PTR [r9+976], rax
	mov rax, QWORD PTR [r9+856]
	mov rcx, QWORD PTR [r9+984]
	mov QWORD PTR [r9+856], rcx
	mov QWORD PTR [r9+984], rax
	mov rax, QWORD PTR [r9+864]
	mov rcx, QWORD PTR [r9+992]
	mov QWORD PTR [r9+864], rcx
	mov QWORD PTR [r9+992], rax
	add rdi, -8
	sub r8, 1
	jne 26b
	sub rdi, -128
	mov rcx, rdx
	cmp rcx, 16
	jb 27f
	mov rcx, 16
	jmp 28f
27:
28:
	mov r10, rsi
	mov rbx, r9
29:
	mov eax, DWORD PTR [rbx+872]
	bswap eax
	mov DWORD PTR [r10], eax
	mov eax, DWORD PTR [rbx+936]
	bswap eax
	mov DWORD PTR [r10+4], eax
	mov eax, DWORD PTR [rbx+744]
	bswap eax
	mov DWORD PTR [r10+8], eax
	mov eax, DWORD PTR [rbx+808]
	bswap eax
	mov DWORD PTR [r10+12], eax
	add r10, 16
	add rbx, 4
	sub rcx, 1
	jne 29b
	mov rcx, rdx
	cmp rcx, 16
	jb 210f
	mov rcx, 16
	jmp 211f
210:
211:
	mov rsi, r10
	sub rdx, rcx
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r9+1000]
	mov rbp, QWORD PTR [r9+1008]
	mov r12, QWORD PTR [r9+1016]
	mov r13, QWORD PTR [r9+1024]
	mov r14, QWORD PTR [r9+1032]
	mov r15, QWORD PTR [r9+1040]
	ret
	.p2align 6
