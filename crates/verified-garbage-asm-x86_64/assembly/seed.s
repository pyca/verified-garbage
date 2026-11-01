// The functions of `src/seed.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_expand_key:
	lea rsp, [rsp-1064]
	mov rdx, rsp
	add rdx, 8
	mov r9, rdx
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
	mov eax, DWORD PTR [rdi]
	bswap eax
	shl rax, 32
	mov r10d, DWORD PTR [rdi+4]
	bswap r10d
	or r10, rax
	mov eax, DWORD PTR [rdi+8]
	bswap eax
	shl rax, 32
	mov r11d, DWORD PTR [rdi+12]
	bswap r11d
	or r11, rax
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -1640531527
	mov DWORD PTR [r9+488], eax
	mov rax, r10
	sub eax, r11d
	add eax, -1640531527
	mov DWORD PTR [r9+492], eax
	ror r10, 8
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, 1013904243
	mov DWORD PTR [r9+496], eax
	mov rax, r10
	sub eax, r11d
	add eax, 1013904243
	mov DWORD PTR [r9+500], eax
	ror r11, 56
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, 2027808486
	mov DWORD PTR [r9+504], eax
	mov rax, r10
	sub eax, r11d
	add eax, 2027808486
	mov DWORD PTR [r9+508], eax
	ror r10, 8
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -239350324
	mov DWORD PTR [r9+512], eax
	mov rax, r10
	sub eax, r11d
	add eax, -239350324
	mov DWORD PTR [r9+516], eax
	ror r11, 56
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -478700647
	mov DWORD PTR [r9+520], eax
	mov rax, r10
	sub eax, r11d
	add eax, -478700647
	mov DWORD PTR [r9+524], eax
	ror r10, 8
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -957401293
	mov DWORD PTR [r9+528], eax
	mov rax, r10
	sub eax, r11d
	add eax, -957401293
	mov DWORD PTR [r9+532], eax
	ror r11, 56
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -1914802585
	mov DWORD PTR [r9+536], eax
	mov rax, r10
	sub eax, r11d
	add eax, -1914802585
	mov DWORD PTR [r9+540], eax
	ror r10, 8
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, 465362127
	mov DWORD PTR [r9+544], eax
	mov rax, r10
	sub eax, r11d
	add eax, 465362127
	mov DWORD PTR [r9+548], eax
	ror r11, 56
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, 930724254
	mov DWORD PTR [r9+552], eax
	mov rax, r10
	sub eax, r11d
	add eax, 930724254
	mov DWORD PTR [r9+556], eax
	ror r10, 8
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, 1861448508
	mov DWORD PTR [r9+560], eax
	mov rax, r10
	sub eax, r11d
	add eax, 1861448508
	mov DWORD PTR [r9+564], eax
	ror r11, 56
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -572070280
	mov DWORD PTR [r9+568], eax
	mov rax, r10
	sub eax, r11d
	add eax, -572070280
	mov DWORD PTR [r9+572], eax
	ror r10, 8
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -1144140559
	mov DWORD PTR [r9+576], eax
	mov rax, r10
	sub eax, r11d
	add eax, -1144140559
	mov DWORD PTR [r9+580], eax
	ror r11, 56
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, 2006686179
	mov DWORD PTR [r9+584], eax
	mov rax, r10
	sub eax, r11d
	add eax, 2006686179
	mov DWORD PTR [r9+588], eax
	ror r10, 8
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -281594938
	mov DWORD PTR [r9+592], eax
	mov rax, r10
	sub eax, r11d
	add eax, -281594938
	mov DWORD PTR [r9+596], eax
	ror r11, 56
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -563189875
	mov DWORD PTR [r9+600], eax
	mov rax, r10
	sub eax, r11d
	add eax, -563189875
	mov DWORD PTR [r9+604], eax
	ror r10, 8
	mov rax, r10
	shr rax, 32
	mov rcx, r11
	shr rcx, 32
	add eax, ecx
	sub eax, -1126379749
	mov DWORD PTR [r9+608], eax
	mov rax, r10
	sub eax, r11d
	add eax, -1126379749
	mov DWORD PTR [r9+612], eax
	ror r11, 56
	mov rdx, rsi
	add rdx, 128
20:
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
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [r9+492]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [r9+496]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [r9+500]
	mov DWORD PTR [rsi+12], eax
	mov eax, DWORD PTR [r9+504]
	mov DWORD PTR [rsi+16], eax
	mov eax, DWORD PTR [r9+508]
	mov DWORD PTR [rsi+20], eax
	mov eax, DWORD PTR [r9+512]
	mov DWORD PTR [rsi+24], eax
	mov eax, DWORD PTR [r9+516]
	mov DWORD PTR [rsi+28], eax
	mov eax, DWORD PTR [r9+520]
	mov DWORD PTR [rsi+32], eax
	mov eax, DWORD PTR [r9+524]
	mov DWORD PTR [rsi+36], eax
	mov eax, DWORD PTR [r9+528]
	mov DWORD PTR [rsi+40], eax
	mov eax, DWORD PTR [r9+532]
	mov DWORD PTR [rsi+44], eax
	mov eax, DWORD PTR [r9+536]
	mov DWORD PTR [rsi+48], eax
	mov eax, DWORD PTR [r9+540]
	mov DWORD PTR [rsi+52], eax
	mov eax, DWORD PTR [r9+544]
	mov DWORD PTR [rsi+56], eax
	mov eax, DWORD PTR [r9+548]
	mov DWORD PTR [rsi+60], eax
	add rsi, 64
	cmp rsi, rdx
	jne 21f
	jmp 22f
21:
	mov eax, DWORD PTR [r9+552]
	mov DWORD PTR [r9+488], eax
	mov eax, DWORD PTR [r9+556]
	mov DWORD PTR [r9+492], eax
	mov eax, DWORD PTR [r9+560]
	mov DWORD PTR [r9+496], eax
	mov eax, DWORD PTR [r9+564]
	mov DWORD PTR [r9+500], eax
	mov eax, DWORD PTR [r9+568]
	mov DWORD PTR [r9+504], eax
	mov eax, DWORD PTR [r9+572]
	mov DWORD PTR [r9+508], eax
	mov eax, DWORD PTR [r9+576]
	mov DWORD PTR [r9+512], eax
	mov eax, DWORD PTR [r9+580]
	mov DWORD PTR [r9+516], eax
	mov eax, DWORD PTR [r9+584]
	mov DWORD PTR [r9+520], eax
	mov eax, DWORD PTR [r9+588]
	mov DWORD PTR [r9+524], eax
	mov eax, DWORD PTR [r9+592]
	mov DWORD PTR [r9+528], eax
	mov eax, DWORD PTR [r9+596]
	mov DWORD PTR [r9+532], eax
	mov eax, DWORD PTR [r9+600]
	mov DWORD PTR [r9+536], eax
	mov eax, DWORD PTR [r9+604]
	mov DWORD PTR [r9+540], eax
	mov eax, DWORD PTR [r9+608]
	mov DWORD PTR [r9+544], eax
	mov eax, DWORD PTR [r9+612]
	mov DWORD PTR [r9+548], eax
	cmp rsi, rdx
22:
	jne 20b
	mov rbx, QWORD PTR [r9+1000]
	mov rbp, QWORD PTR [r9+1008]
	mov r12, QWORD PTR [r9+1016]
	mov r13, QWORD PTR [r9+1024]
	mov r14, QWORD PTR [r9+1032]
	mov r15, QWORD PTR [r9+1040]
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
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	lea rsp, [rsp+1064]
	ret
	.p2align 6

vg_seed_ecb_encrypt:
	lea rsp, [rsp-1096]
	mov rcx, rsp
	add rcx, 8
	call {vg_seed_encrypt_blocks}
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
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	lea rsp, [rsp+1096]
	ret
	.p2align 6

vg_seed_ecb_decrypt:
	lea rsp, [rsp-1096]
	mov rcx, rsp
	add rcx, 8
	call {vg_seed_decrypt_blocks}
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
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	lea rsp, [rsp+1096]
	ret
	.p2align 6
