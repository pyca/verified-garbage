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
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	lea rsp, [rsp+1064]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	lea rsp, [rsp-1056]
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+1056]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_seed_ecb_encrypt:
	lea rsp, [rsp-1096]
	mov rcx, rsp
	add rcx, 8
	call {vg_seed_encrypt_blocks}
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	lea rsp, [rsp+1096]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	lea rsp, [rsp-1096]
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+1096]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_seed_ecb_decrypt:
	lea rsp, [rsp-1096]
	mov rcx, rsp
	add rcx, 8
	call {vg_seed_decrypt_blocks}
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	lea rsp, [rsp+1096]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	lea rsp, [rsp-1096]
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+1096]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6
