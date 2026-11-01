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
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+408], r14
	movabs r14, -71777214294589696
	mov QWORD PTR [r9+416], r14
	movabs r14, -3459661728999223300
	mov QWORD PTR [r9+424], r14
	movabs r14, 68468732266233843
	mov QWORD PTR [r9+432], r14
	movabs r14, 4539628425446424576
	mov QWORD PTR [r9+440], r14
	movabs r14, 277965988494543
	mov QWORD PTR [r9+448], r14
	movabs r14, -229965051731181568
	mov QWORD PTR [r9+456], r14
	movabs r14, 270582939711
	mov QWORD PTR [r9+464], r14
	movabs r14, -918748613553687808
	mov QWORD PTR [r9+472], r14
	movabs r14, -1789082251201616085
	mov QWORD PTR [r9+480], r14
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
	mov rbx, QWORD PTR [r9+496]
	mov rcx, QWORD PTR [r9+504]
	mov rbp, QWORD PTR [r9+512]
	mov r10, QWORD PTR [r9+520]
	mov r11, QWORD PTR [r9+528]
	mov r12, QWORD PTR [r9+536]
	mov r13, QWORD PTR [r9+544]
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [r9+8], rax
	mov QWORD PTR [r9+16], rbx
	mov QWORD PTR [r9+24], rcx
	mov QWORD PTR [r9+32], rbp
	mov QWORD PTR [r9+40], r10
	mov QWORD PTR [r9+48], r11
	mov QWORD PTR [r9+56], r12
	mov QWORD PTR [r9+64], r13
	mov rax, QWORD PTR [r9+8]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9+32]
	mov rbx, QWORD PTR [r9+24]
	xor rbx, QWORD PTR [r9+32]
	xor rbx, QWORD PTR [r9+56]
	xor rbx, QWORD PTR [r9+64]
	mov rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9+48]
	xor rcx, QWORD PTR [r9+64]
	mov rbp, QWORD PTR [r9+16]
	xor rbp, QWORD PTR [r9+24]
	xor rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+48]
	mov r10, QWORD PTR [r9+16]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9+40]
	mov r11, QWORD PTR [r9+32]
	xor r11, QWORD PTR [r9+40]
	mov r12, QWORD PTR [r9+24]
	xor r12, QWORD PTR [r9+32]
	xor r12, QWORD PTR [r9+40]
	xor r12, QWORD PTR [r9+48]
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+48]
	xor r13, QWORD PTR [r9+56]
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r10
	xor r14, rcx
	mov r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+8], rbp
	mov rbp, r13
	xor rbp, r10
	mov QWORD PTR [r9+16], rbp
	mov rbp, r13
	xor rbp, rcx
	xor r11, r12
	mov QWORD PTR [r9+24], r12
	mov r12, r11
	xor r12, rax
	xor r10, r12
	mov QWORD PTR [r9+32], r10
	mov r10, r15
	xor r10, r14
	mov QWORD PTR [r9+40], r14
	mov r14, r12
	xor r14, r13
	xor rbx, r12
	mov QWORD PTR [r9+48], r14
	mov r14, rbx
	xor r14, rbp
	mov QWORD PTR [r9+56], rbx
	mov rbx, QWORD PTR [r9+8]
	xor rbx, r10
	xor rcx, rbx
	xor rbx, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], r12
	mov r12, rcx
	xor r12, rax
	mov QWORD PTR [r9+8], r12
	mov r12, rcx
	xor r12, r11
	mov QWORD PTR [r9+64], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+16]
	mov QWORD PTR [r9+72], rbx
	mov rbx, rax
	xor rbx, r14
	mov QWORD PTR [r9+80], rbx
	mov rbx, r12
	xor rbx, r14
	mov QWORD PTR [r9+88], rbx
	mov rbx, r12
	xor rbx, rbp
	xor r11, r14
	mov QWORD PTR [r9+96], rbx
	mov rbx, r15
	xor rbx, r11
	xor r13, r11
	mov QWORD PTR [r9+104], r13
	mov r13, r10
	and r13, rcx
	mov QWORD PTR [r9+112], r10
	mov r10, QWORD PTR [r9+64]
	and r10, QWORD PTR [r9+8]
	xor r10, r13
	mov QWORD PTR [r9+120], rcx
	mov rcx, QWORD PTR [r9+32]
	and rcx, rax
	xor rcx, r13
	mov r13, r15
	and r13, r11
	mov QWORD PTR [r9+128], r15
	mov r15, QWORD PTR [r9+56]
	and r15, QWORD PTR [r9+24]
	xor r15, r13
	mov QWORD PTR [r9+136], r11
	mov r11, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+80]
	xor r11, r13
	mov r13, QWORD PTR [r9+16]
	and r13, r14
	mov QWORD PTR [r9+144], r14
	mov r14, QWORD PTR [r9+40]
	and r14, QWORD PTR [r9+88]
	xor r14, r13
	mov QWORD PTR [r9+152], rax
	mov rax, rbp
	and rax, r12
	xor rax, r13
	xor r10, r14
	xor rcx, rax
	xor r15, r14
	xor r11, rax
	xor r10, QWORD PTR [r9+72]
	xor rcx, QWORD PTR [r9+96]
	xor r15, rbx
	xor r11, QWORD PTR [r9+104]
	mov rbx, r10
	xor rbx, rcx
	and r10, r15
	mov rax, r11
	xor rax, r10
	mov r14, rbx
	and r14, rax
	xor r14, rcx
	mov r13, r15
	xor r13, r11
	xor rcx, r10
	and rcx, r13
	xor rcx, r11
	xor r15, rcx
	mov r13, rax
	xor r13, rcx
	and r11, r13
	xor r15, r11
	xor rax, r11
	and rax, r14
	xor rbx, rax
	mov rax, rbx
	xor rax, r15
	mov r11, r14
	xor r11, rcx
	mov r13, r14
	xor r13, rbx
	mov r10, rcx
	xor r10, r15
	mov QWORD PTR [r9+104], rbp
	mov rbp, r11
	xor rbp, rax
	mov QWORD PTR [r9+96], rax
	mov rax, r10
	and rax, QWORD PTR [r9+120]
	mov QWORD PTR [r9+120], rax
	mov rax, r15
	and rax, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], rax
	mov rax, rcx
	and rax, QWORD PTR [r9+152]
	mov QWORD PTR [r9+152], rax
	mov rax, r13
	and rax, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], rax
	mov rax, rbx
	and rax, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], rax
	mov rax, r14
	and rax, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, r11
	and rax, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rax
	mov rax, rbp
	and rax, QWORD PTR [r9+88]
	and r12, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+112]
	and r15, QWORD PTR [r9+64]
	and rcx, QWORD PTR [r9+32]
	and r13, QWORD PTR [r9+128]
	and rbx, QWORD PTR [r9+56]
	and r14, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+16]
	and rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r14
	mov r14, QWORD PTR [r9+96]
	and r14, QWORD PTR [r9+104]
	xor r11, rbp
	xor rcx, r15
	xor rbx, QWORD PTR [r9+80]
	xor r10, r15
	mov r15, QWORD PTR [r9+152]
	xor r15, r13
	mov QWORD PTR [r9+104], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rax
	mov QWORD PTR [r9+80], rcx
	mov rcx, QWORD PTR [r9+120]
	xor rcx, QWORD PTR [r9+136]
	xor rax, QWORD PTR [r9+144]
	xor rbp, r14
	xor r13, rbx
	xor r15, rcx
	mov r14, QWORD PTR [r9+24]
	xor r14, r11
	xor rax, QWORD PTR [r9+136]
	xor r11, r15
	xor r15, QWORD PTR [r9+40]
	xor r12, r14
	xor r10, r14
	mov r14, QWORD PTR [r9+24]
	xor r14, rax
	xor r15, r12
	mov QWORD PTR [r9+24], rbp
	mov rbp, QWORD PTR [r9+8]
	xor rbp, r10
	xor rax, r10
	xor r13, r12
	xor r13, QWORD PTR [r9]
	xor rbx, r11
	xor rbx, QWORD PTR [r9]
	mov r11, r14
	xor r11, r15
	xor rcx, rbp
	xor rbp, QWORD PTR [r9+80]
	xor r15, QWORD PTR [r9+104]
	xor r14, rcx
	xor r14, QWORD PTR [r9]
	xor r11, QWORD PTR [r9+24]
	xor r11, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r13
	mov r13, rax
	mov r12, r14
	mov r10, rcx
	mov rcx, r15
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+24]
	mov rax, QWORD PTR [r9+104]
	mov QWORD PTR [r9+8], rax
	mov QWORD PTR [r9+16], rbx
	mov QWORD PTR [r9+24], rcx
	mov QWORD PTR [r9+32], rbp
	mov QWORD PTR [r9+40], r10
	mov QWORD PTR [r9+48], r11
	mov QWORD PTR [r9+56], r12
	mov QWORD PTR [r9+64], r13
	mov rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9+40]
	xor rax, QWORD PTR [r9+48]
	xor rax, QWORD PTR [r9+56]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	and rax, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov rbx, QWORD PTR [r9+24]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+48]
	mov r15, QWORD PTR [r9+40]
	xor r15, QWORD PTR [r9+56]
	xor r15, QWORD PTR [r9+64]
	and rbx, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	xor rbx, r15
	mov rcx, QWORD PTR [r9+16]
	mov r14, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+32]
	mov r15, QWORD PTR [r9+8]
	xor r15, QWORD PTR [r9+40]
	xor r15, QWORD PTR [r9+56]
	and rcx, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	xor rcx, r15
	mov rbp, QWORD PTR [r9+24]
	xor rbp, QWORD PTR [r9+64]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov r15, QWORD PTR [r9+8]
	xor r15, QWORD PTR [r9+40]
	xor r15, QWORD PTR [r9+48]
	xor r15, QWORD PTR [r9+56]
	and rbp, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	xor rbp, r15
	mov r10, QWORD PTR [r9+8]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9+40]
	mov r14, QWORD PTR [r9+64]
	mov r15, QWORD PTR [r9+32]
	xor r15, QWORD PTR [r9+56]
	and r10, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	xor r10, r15
	mov r11, QWORD PTR [r9+8]
	xor r11, QWORD PTR [r9+16]
	mov r14, QWORD PTR [r9+40]
	mov r15, QWORD PTR [r9+32]
	xor r15, QWORD PTR [r9+48]
	xor r15, QWORD PTR [r9+56]
	and r11, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	xor r11, r15
	mov r12, QWORD PTR [r9+8]
	xor r12, QWORD PTR [r9+40]
	xor r12, QWORD PTR [r9+48]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+32]
	mov r15, QWORD PTR [r9+56]
	and r12, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	xor r12, r15
	mov r13, QWORD PTR [r9+16]
	xor r13, QWORD PTR [r9+56]
	xor r13, QWORD PTR [r9+64]
	and r13, QWORD PTR [r9+408]
	xor r13, QWORD PTR [r9+32]
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r15, rax
	and r15, QWORD PTR [r9+424]
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rax
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rax
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rax
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+488], r15
	mov r15, rbx
	and r15, QWORD PTR [r9+424]
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rbx
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rbx
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rbx
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+496], r15
	mov r15, rcx
	and r15, QWORD PTR [r9+424]
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rcx
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rcx
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rcx
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+504], r15
	mov r15, rbp
	and r15, QWORD PTR [r9+424]
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rbp
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rbp
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rbp
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+512], r15
	mov r15, r10
	and r15, QWORD PTR [r9+424]
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r10
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r10
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r10
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+520], r15
	mov r15, r11
	and r15, QWORD PTR [r9+424]
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r11
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r11
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r11
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+528], r15
	mov r15, r12
	and r15, QWORD PTR [r9+424]
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r12
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r12
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r12
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+536], r15
	mov r15, r13
	and r15, QWORD PTR [r9+424]
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r13
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r13
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r13
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+544], r15
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
	mov rbx, QWORD PTR [r9+496]
	mov rcx, QWORD PTR [r9+504]
	mov rbp, QWORD PTR [r9+512]
	mov r10, QWORD PTR [r9+520]
	mov r11, QWORD PTR [r9+528]
	mov r12, QWORD PTR [r9+536]
	mov r13, QWORD PTR [r9+544]
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [r9+8], rax
	mov QWORD PTR [r9+16], rbx
	mov QWORD PTR [r9+24], rcx
	mov QWORD PTR [r9+32], rbp
	mov QWORD PTR [r9+40], r10
	mov QWORD PTR [r9+48], r11
	mov QWORD PTR [r9+56], r12
	mov QWORD PTR [r9+64], r13
	mov rax, QWORD PTR [r9+8]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9+32]
	mov rbx, QWORD PTR [r9+24]
	xor rbx, QWORD PTR [r9+32]
	xor rbx, QWORD PTR [r9+56]
	xor rbx, QWORD PTR [r9+64]
	mov rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9+48]
	xor rcx, QWORD PTR [r9+64]
	mov rbp, QWORD PTR [r9+16]
	xor rbp, QWORD PTR [r9+24]
	xor rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+48]
	mov r10, QWORD PTR [r9+16]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9+40]
	mov r11, QWORD PTR [r9+32]
	xor r11, QWORD PTR [r9+40]
	mov r12, QWORD PTR [r9+24]
	xor r12, QWORD PTR [r9+32]
	xor r12, QWORD PTR [r9+40]
	xor r12, QWORD PTR [r9+48]
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+48]
	xor r13, QWORD PTR [r9+56]
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r10
	xor r14, rcx
	mov r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+8], rbp
	mov rbp, r13
	xor rbp, r10
	mov QWORD PTR [r9+16], rbp
	mov rbp, r13
	xor rbp, rcx
	xor r11, r12
	mov QWORD PTR [r9+24], r12
	mov r12, r11
	xor r12, rax
	xor r10, r12
	mov QWORD PTR [r9+32], r10
	mov r10, r15
	xor r10, r14
	mov QWORD PTR [r9+40], r14
	mov r14, r12
	xor r14, r13
	xor rbx, r12
	mov QWORD PTR [r9+48], r14
	mov r14, rbx
	xor r14, rbp
	mov QWORD PTR [r9+56], rbx
	mov rbx, QWORD PTR [r9+8]
	xor rbx, r10
	xor rcx, rbx
	xor rbx, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], r12
	mov r12, rcx
	xor r12, rax
	mov QWORD PTR [r9+8], r12
	mov r12, rcx
	xor r12, r11
	mov QWORD PTR [r9+64], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+16]
	mov QWORD PTR [r9+72], rbx
	mov rbx, rax
	xor rbx, r14
	mov QWORD PTR [r9+80], rbx
	mov rbx, r12
	xor rbx, r14
	mov QWORD PTR [r9+88], rbx
	mov rbx, r12
	xor rbx, rbp
	xor r11, r14
	mov QWORD PTR [r9+96], rbx
	mov rbx, r15
	xor rbx, r11
	xor r13, r11
	mov QWORD PTR [r9+104], r13
	mov r13, r10
	and r13, rcx
	mov QWORD PTR [r9+112], r10
	mov r10, QWORD PTR [r9+64]
	and r10, QWORD PTR [r9+8]
	xor r10, r13
	mov QWORD PTR [r9+120], rcx
	mov rcx, QWORD PTR [r9+32]
	and rcx, rax
	xor rcx, r13
	mov r13, r15
	and r13, r11
	mov QWORD PTR [r9+128], r15
	mov r15, QWORD PTR [r9+56]
	and r15, QWORD PTR [r9+24]
	xor r15, r13
	mov QWORD PTR [r9+136], r11
	mov r11, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+80]
	xor r11, r13
	mov r13, QWORD PTR [r9+16]
	and r13, r14
	mov QWORD PTR [r9+144], r14
	mov r14, QWORD PTR [r9+40]
	and r14, QWORD PTR [r9+88]
	xor r14, r13
	mov QWORD PTR [r9+152], rax
	mov rax, rbp
	and rax, r12
	xor rax, r13
	xor r10, r14
	xor rcx, rax
	xor r15, r14
	xor r11, rax
	xor r10, QWORD PTR [r9+72]
	xor rcx, QWORD PTR [r9+96]
	xor r15, rbx
	xor r11, QWORD PTR [r9+104]
	mov rbx, r10
	xor rbx, rcx
	and r10, r15
	mov rax, r11
	xor rax, r10
	mov r14, rbx
	and r14, rax
	xor r14, rcx
	mov r13, r15
	xor r13, r11
	xor rcx, r10
	and rcx, r13
	xor rcx, r11
	xor r15, rcx
	mov r13, rax
	xor r13, rcx
	and r11, r13
	xor r15, r11
	xor rax, r11
	and rax, r14
	xor rbx, rax
	mov rax, rbx
	xor rax, r15
	mov r11, r14
	xor r11, rcx
	mov r13, r14
	xor r13, rbx
	mov r10, rcx
	xor r10, r15
	mov QWORD PTR [r9+104], rbp
	mov rbp, r11
	xor rbp, rax
	mov QWORD PTR [r9+96], rax
	mov rax, r10
	and rax, QWORD PTR [r9+120]
	mov QWORD PTR [r9+120], rax
	mov rax, r15
	and rax, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], rax
	mov rax, rcx
	and rax, QWORD PTR [r9+152]
	mov QWORD PTR [r9+152], rax
	mov rax, r13
	and rax, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], rax
	mov rax, rbx
	and rax, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], rax
	mov rax, r14
	and rax, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, r11
	and rax, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rax
	mov rax, rbp
	and rax, QWORD PTR [r9+88]
	and r12, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+112]
	and r15, QWORD PTR [r9+64]
	and rcx, QWORD PTR [r9+32]
	and r13, QWORD PTR [r9+128]
	and rbx, QWORD PTR [r9+56]
	and r14, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+16]
	and rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r14
	mov r14, QWORD PTR [r9+96]
	and r14, QWORD PTR [r9+104]
	xor r11, rbp
	xor rcx, r15
	xor rbx, QWORD PTR [r9+80]
	xor r10, r15
	mov r15, QWORD PTR [r9+152]
	xor r15, r13
	mov QWORD PTR [r9+104], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rax
	mov QWORD PTR [r9+80], rcx
	mov rcx, QWORD PTR [r9+120]
	xor rcx, QWORD PTR [r9+136]
	xor rax, QWORD PTR [r9+144]
	xor rbp, r14
	xor r13, rbx
	xor r15, rcx
	mov r14, QWORD PTR [r9+24]
	xor r14, r11
	xor rax, QWORD PTR [r9+136]
	xor r11, r15
	xor r15, QWORD PTR [r9+40]
	xor r12, r14
	xor r10, r14
	mov r14, QWORD PTR [r9+24]
	xor r14, rax
	xor r15, r12
	mov QWORD PTR [r9+24], rbp
	mov rbp, QWORD PTR [r9+8]
	xor rbp, r10
	xor rax, r10
	xor r13, r12
	xor r13, QWORD PTR [r9]
	xor rbx, r11
	xor rbx, QWORD PTR [r9]
	mov r11, r14
	xor r11, r15
	xor rcx, rbp
	xor rbp, QWORD PTR [r9+80]
	xor r15, QWORD PTR [r9+104]
	xor r14, rcx
	xor r14, QWORD PTR [r9]
	xor r11, QWORD PTR [r9+24]
	xor r11, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r13
	mov r13, rax
	mov r12, r14
	mov r10, rcx
	mov rcx, r15
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+24]
	mov rax, QWORD PTR [r9+104]
	mov QWORD PTR [r9+8], rax
	mov QWORD PTR [r9+16], rbx
	mov QWORD PTR [r9+24], rcx
	mov QWORD PTR [r9+32], rbp
	mov QWORD PTR [r9+40], r10
	mov QWORD PTR [r9+48], r11
	mov QWORD PTR [r9+56], r12
	mov QWORD PTR [r9+64], r13
	mov rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9+40]
	xor rax, QWORD PTR [r9+48]
	xor rax, QWORD PTR [r9+56]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	and rax, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov rbx, QWORD PTR [r9+24]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+48]
	mov r15, QWORD PTR [r9+40]
	xor r15, QWORD PTR [r9+56]
	xor r15, QWORD PTR [r9+64]
	and rbx, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	xor rbx, r15
	mov rcx, QWORD PTR [r9+16]
	mov r14, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+32]
	mov r15, QWORD PTR [r9+8]
	xor r15, QWORD PTR [r9+40]
	xor r15, QWORD PTR [r9+56]
	and rcx, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	xor rcx, r15
	mov rbp, QWORD PTR [r9+24]
	xor rbp, QWORD PTR [r9+64]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov r15, QWORD PTR [r9+8]
	xor r15, QWORD PTR [r9+40]
	xor r15, QWORD PTR [r9+48]
	xor r15, QWORD PTR [r9+56]
	and rbp, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	xor rbp, r15
	mov r10, QWORD PTR [r9+8]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9+40]
	mov r14, QWORD PTR [r9+64]
	mov r15, QWORD PTR [r9+32]
	xor r15, QWORD PTR [r9+56]
	and r10, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	xor r10, r15
	mov r11, QWORD PTR [r9+8]
	xor r11, QWORD PTR [r9+16]
	mov r14, QWORD PTR [r9+40]
	mov r15, QWORD PTR [r9+32]
	xor r15, QWORD PTR [r9+48]
	xor r15, QWORD PTR [r9+56]
	and r11, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	xor r11, r15
	mov r12, QWORD PTR [r9+8]
	xor r12, QWORD PTR [r9+40]
	xor r12, QWORD PTR [r9+48]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+32]
	mov r15, QWORD PTR [r9+56]
	and r12, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	xor r12, r15
	mov r13, QWORD PTR [r9+16]
	xor r13, QWORD PTR [r9+56]
	xor r13, QWORD PTR [r9+64]
	and r13, QWORD PTR [r9+408]
	xor r13, QWORD PTR [r9+32]
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r15, rax
	and r15, QWORD PTR [r9+424]
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rax
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rax
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rax
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+488], r15
	mov r15, rbx
	and r15, QWORD PTR [r9+424]
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rbx
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rbx
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rbx
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+496], r15
	mov r15, rcx
	and r15, QWORD PTR [r9+424]
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rcx
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rcx
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rcx
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+504], r15
	mov r15, rbp
	and r15, QWORD PTR [r9+424]
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rbp
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rbp
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rbp
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+512], r15
	mov r15, r10
	and r15, QWORD PTR [r9+424]
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r10
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r10
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r10
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+520], r15
	mov r15, r11
	and r15, QWORD PTR [r9+424]
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r11
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r11
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r11
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+528], r15
	mov r15, r12
	and r15, QWORD PTR [r9+424]
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r12
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r12
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r12
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+536], r15
	mov r15, r13
	and r15, QWORD PTR [r9+424]
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r13
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r13
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r13
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+544], r15
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
	mov rbx, QWORD PTR [r9+496]
	mov rcx, QWORD PTR [r9+504]
	mov rbp, QWORD PTR [r9+512]
	mov r10, QWORD PTR [r9+520]
	mov r11, QWORD PTR [r9+528]
	mov r12, QWORD PTR [r9+536]
	mov r13, QWORD PTR [r9+544]
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [r9+8], rax
	mov QWORD PTR [r9+16], rbx
	mov QWORD PTR [r9+24], rcx
	mov QWORD PTR [r9+32], rbp
	mov QWORD PTR [r9+40], r10
	mov QWORD PTR [r9+48], r11
	mov QWORD PTR [r9+56], r12
	mov QWORD PTR [r9+64], r13
	mov rax, QWORD PTR [r9+8]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9+32]
	mov rbx, QWORD PTR [r9+24]
	xor rbx, QWORD PTR [r9+32]
	xor rbx, QWORD PTR [r9+56]
	xor rbx, QWORD PTR [r9+64]
	mov rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9+48]
	xor rcx, QWORD PTR [r9+64]
	mov rbp, QWORD PTR [r9+16]
	xor rbp, QWORD PTR [r9+24]
	xor rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+48]
	mov r10, QWORD PTR [r9+16]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9+40]
	mov r11, QWORD PTR [r9+32]
	xor r11, QWORD PTR [r9+40]
	mov r12, QWORD PTR [r9+24]
	xor r12, QWORD PTR [r9+32]
	xor r12, QWORD PTR [r9+40]
	xor r12, QWORD PTR [r9+48]
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+48]
	xor r13, QWORD PTR [r9+56]
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r10
	xor r14, rcx
	mov r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+8], rbp
	mov rbp, r13
	xor rbp, r10
	mov QWORD PTR [r9+16], rbp
	mov rbp, r13
	xor rbp, rcx
	xor r11, r12
	mov QWORD PTR [r9+24], r12
	mov r12, r11
	xor r12, rax
	xor r10, r12
	mov QWORD PTR [r9+32], r10
	mov r10, r15
	xor r10, r14
	mov QWORD PTR [r9+40], r14
	mov r14, r12
	xor r14, r13
	xor rbx, r12
	mov QWORD PTR [r9+48], r14
	mov r14, rbx
	xor r14, rbp
	mov QWORD PTR [r9+56], rbx
	mov rbx, QWORD PTR [r9+8]
	xor rbx, r10
	xor rcx, rbx
	xor rbx, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], r12
	mov r12, rcx
	xor r12, rax
	mov QWORD PTR [r9+8], r12
	mov r12, rcx
	xor r12, r11
	mov QWORD PTR [r9+64], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+16]
	mov QWORD PTR [r9+72], rbx
	mov rbx, rax
	xor rbx, r14
	mov QWORD PTR [r9+80], rbx
	mov rbx, r12
	xor rbx, r14
	mov QWORD PTR [r9+88], rbx
	mov rbx, r12
	xor rbx, rbp
	xor r11, r14
	mov QWORD PTR [r9+96], rbx
	mov rbx, r15
	xor rbx, r11
	xor r13, r11
	mov QWORD PTR [r9+104], r13
	mov r13, r10
	and r13, rcx
	mov QWORD PTR [r9+112], r10
	mov r10, QWORD PTR [r9+64]
	and r10, QWORD PTR [r9+8]
	xor r10, r13
	mov QWORD PTR [r9+120], rcx
	mov rcx, QWORD PTR [r9+32]
	and rcx, rax
	xor rcx, r13
	mov r13, r15
	and r13, r11
	mov QWORD PTR [r9+128], r15
	mov r15, QWORD PTR [r9+56]
	and r15, QWORD PTR [r9+24]
	xor r15, r13
	mov QWORD PTR [r9+136], r11
	mov r11, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+80]
	xor r11, r13
	mov r13, QWORD PTR [r9+16]
	and r13, r14
	mov QWORD PTR [r9+144], r14
	mov r14, QWORD PTR [r9+40]
	and r14, QWORD PTR [r9+88]
	xor r14, r13
	mov QWORD PTR [r9+152], rax
	mov rax, rbp
	and rax, r12
	xor rax, r13
	xor r10, r14
	xor rcx, rax
	xor r15, r14
	xor r11, rax
	xor r10, QWORD PTR [r9+72]
	xor rcx, QWORD PTR [r9+96]
	xor r15, rbx
	xor r11, QWORD PTR [r9+104]
	mov rbx, r10
	xor rbx, rcx
	and r10, r15
	mov rax, r11
	xor rax, r10
	mov r14, rbx
	and r14, rax
	xor r14, rcx
	mov r13, r15
	xor r13, r11
	xor rcx, r10
	and rcx, r13
	xor rcx, r11
	xor r15, rcx
	mov r13, rax
	xor r13, rcx
	and r11, r13
	xor r15, r11
	xor rax, r11
	and rax, r14
	xor rbx, rax
	mov rax, rbx
	xor rax, r15
	mov r11, r14
	xor r11, rcx
	mov r13, r14
	xor r13, rbx
	mov r10, rcx
	xor r10, r15
	mov QWORD PTR [r9+104], rbp
	mov rbp, r11
	xor rbp, rax
	mov QWORD PTR [r9+96], rax
	mov rax, r10
	and rax, QWORD PTR [r9+120]
	mov QWORD PTR [r9+120], rax
	mov rax, r15
	and rax, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], rax
	mov rax, rcx
	and rax, QWORD PTR [r9+152]
	mov QWORD PTR [r9+152], rax
	mov rax, r13
	and rax, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], rax
	mov rax, rbx
	and rax, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], rax
	mov rax, r14
	and rax, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, r11
	and rax, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rax
	mov rax, rbp
	and rax, QWORD PTR [r9+88]
	and r12, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+112]
	and r15, QWORD PTR [r9+64]
	and rcx, QWORD PTR [r9+32]
	and r13, QWORD PTR [r9+128]
	and rbx, QWORD PTR [r9+56]
	and r14, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+16]
	and rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r14
	mov r14, QWORD PTR [r9+96]
	and r14, QWORD PTR [r9+104]
	xor r11, rbp
	xor rcx, r15
	xor rbx, QWORD PTR [r9+80]
	xor r10, r15
	mov r15, QWORD PTR [r9+152]
	xor r15, r13
	mov QWORD PTR [r9+104], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rax
	mov QWORD PTR [r9+80], rcx
	mov rcx, QWORD PTR [r9+120]
	xor rcx, QWORD PTR [r9+136]
	xor rax, QWORD PTR [r9+144]
	xor rbp, r14
	xor r13, rbx
	xor r15, rcx
	mov r14, QWORD PTR [r9+24]
	xor r14, r11
	xor rax, QWORD PTR [r9+136]
	xor r11, r15
	xor r15, QWORD PTR [r9+40]
	xor r12, r14
	xor r10, r14
	mov r14, QWORD PTR [r9+24]
	xor r14, rax
	xor r15, r12
	mov QWORD PTR [r9+24], rbp
	mov rbp, QWORD PTR [r9+8]
	xor rbp, r10
	xor rax, r10
	xor r13, r12
	xor r13, QWORD PTR [r9]
	xor rbx, r11
	xor rbx, QWORD PTR [r9]
	mov r11, r14
	xor r11, r15
	xor rcx, rbp
	xor rbp, QWORD PTR [r9+80]
	xor r15, QWORD PTR [r9+104]
	xor r14, rcx
	xor r14, QWORD PTR [r9]
	xor r11, QWORD PTR [r9+24]
	xor r11, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r13
	mov r13, rax
	mov r12, r14
	mov r10, rcx
	mov rcx, r15
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+24]
	mov rax, QWORD PTR [r9+104]
	mov QWORD PTR [r9+8], rax
	mov QWORD PTR [r9+16], rbx
	mov QWORD PTR [r9+24], rcx
	mov QWORD PTR [r9+32], rbp
	mov QWORD PTR [r9+40], r10
	mov QWORD PTR [r9+48], r11
	mov QWORD PTR [r9+56], r12
	mov QWORD PTR [r9+64], r13
	mov rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9+40]
	xor rax, QWORD PTR [r9+48]
	xor rax, QWORD PTR [r9+56]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	and rax, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov rbx, QWORD PTR [r9+24]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+48]
	mov r15, QWORD PTR [r9+40]
	xor r15, QWORD PTR [r9+56]
	xor r15, QWORD PTR [r9+64]
	and rbx, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	xor rbx, r15
	mov rcx, QWORD PTR [r9+16]
	mov r14, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+32]
	mov r15, QWORD PTR [r9+8]
	xor r15, QWORD PTR [r9+40]
	xor r15, QWORD PTR [r9+56]
	and rcx, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	xor rcx, r15
	mov rbp, QWORD PTR [r9+24]
	xor rbp, QWORD PTR [r9+64]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov r15, QWORD PTR [r9+8]
	xor r15, QWORD PTR [r9+40]
	xor r15, QWORD PTR [r9+48]
	xor r15, QWORD PTR [r9+56]
	and rbp, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	xor rbp, r15
	mov r10, QWORD PTR [r9+8]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9+40]
	mov r14, QWORD PTR [r9+64]
	mov r15, QWORD PTR [r9+32]
	xor r15, QWORD PTR [r9+56]
	and r10, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	xor r10, r15
	mov r11, QWORD PTR [r9+8]
	xor r11, QWORD PTR [r9+16]
	mov r14, QWORD PTR [r9+40]
	mov r15, QWORD PTR [r9+32]
	xor r15, QWORD PTR [r9+48]
	xor r15, QWORD PTR [r9+56]
	and r11, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	xor r11, r15
	mov r12, QWORD PTR [r9+8]
	xor r12, QWORD PTR [r9+40]
	xor r12, QWORD PTR [r9+48]
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+32]
	mov r15, QWORD PTR [r9+56]
	and r12, QWORD PTR [r9+408]
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	xor r12, r15
	mov r13, QWORD PTR [r9+16]
	xor r13, QWORD PTR [r9+56]
	xor r13, QWORD PTR [r9+64]
	and r13, QWORD PTR [r9+408]
	xor r13, QWORD PTR [r9+32]
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r15, rax
	and r15, QWORD PTR [r9+424]
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rax
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rax
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rax
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+488], r15
	mov r15, rbx
	and r15, QWORD PTR [r9+424]
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rbx
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rbx
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rbx
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+496], r15
	mov r15, rcx
	and r15, QWORD PTR [r9+424]
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rcx
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rcx
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rcx
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+504], r15
	mov r15, rbp
	and r15, QWORD PTR [r9+424]
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, rbp
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, rbp
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, rbp
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+512], r15
	mov r15, r10
	and r15, QWORD PTR [r9+424]
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r10
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r10
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r10
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+520], r15
	mov r15, r11
	and r15, QWORD PTR [r9+424]
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r11
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r11
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r11
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+528], r15
	mov r15, r12
	and r15, QWORD PTR [r9+424]
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r12
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r12
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r12
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+536], r15
	mov r15, r13
	and r15, QWORD PTR [r9+424]
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+432]
	xor r15, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+440]
	xor r15, r14
	mov r14, r13
	ror r14, 16
	and r14, QWORD PTR [r9+448]
	xor r15, r14
	mov r14, r13
	ror r14, 48
	and r14, QWORD PTR [r9+456]
	xor r15, r14
	mov r14, r13
	ror r14, 24
	and r14, QWORD PTR [r9+464]
	xor r15, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+472]
	xor r15, r14
	xor r15, QWORD PTR [r9+480]
	mov QWORD PTR [r9+544], r15
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
