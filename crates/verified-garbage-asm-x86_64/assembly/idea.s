// The functions of `src/idea.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_idea_expand_key:
	mov rdx, QWORD PTR [rdi]
	ror rdx, 8
	movabs rcx, 71777214294589695
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 56
	movabs rcx, -71777214294589696
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi], rax
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 8
	movabs rcx, 71777214294589695
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 56
	movabs rcx, -71777214294589696
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+8], rax
	mov rdx, QWORD PTR [rdi]
	ror rdx, 47
	movabs rcx, 65537
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 31
	movabs rcx, 33423870
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 15
	movabs rcx, 279280214932992
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 47
	movabs rcx, 281479271677952
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 31
	movabs rcx, 143554428555755520
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 15
	movabs rcx, -144115188075855872
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+16], rax
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 47
	movabs rcx, 65537
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 31
	movabs rcx, 33423870
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 15
	movabs rcx, 279280214932992
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 47
	movabs rcx, 281479271677952
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 31
	movabs rcx, 143554428555755520
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 15
	movabs rcx, -144115188075855872
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+24], rax
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 6
	movabs rcx, 844437815230467
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 54
	movabs rcx, 1020
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 38
	movabs rcx, 64512
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 54
	movabs rcx, 287108857178357760
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 38
	movabs rcx, -287953294993653760
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+32], rax
	mov rdx, QWORD PTR [rdi]
	ror rdx, 6
	movabs rcx, 844437815230467
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 54
	movabs rcx, 1020
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 38
	movabs rcx, 64512
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 54
	movabs rcx, 287108857178357760
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 38
	movabs rcx, -287953294993653760
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+40], rax
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 29
	movabs rcx, 30065229831
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 13
	movabs rcx, 8761866979320
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 61
	movabs rcx, -576188069258921984
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 29
	movabs rcx, 1970324836974592
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 13
	movabs rcx, 574208952489738240
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+48], rax
	mov rdx, QWORD PTR [rdi]
	ror rdx, 29
	movabs rcx, 30065229831
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 13
	movabs rcx, 8761866979320
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 61
	movabs rcx, -576188069258921984
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 29
	movabs rcx, 1970324836974592
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 13
	movabs rcx, 574208952489738240
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+56], rax
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 52
	movabs rcx, 15
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 36
	movabs rcx, 267390960
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 20
	movabs rcx, 4026593280
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 52
	movabs rcx, 4222189076152320
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 36
	movabs rcx, 1148435428446044160
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 20
	movabs rcx, -1152657621816180736
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+64], rax
	mov rdx, QWORD PTR [rdi]
	ror rdx, 52
	movabs rcx, 15
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 36
	movabs rcx, 267390960
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 20
	movabs rcx, 4026593280
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 52
	movabs rcx, 4222189076152320
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 36
	movabs rcx, 1148435428446044160
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 20
	movabs rcx, -1152657621816180736
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+72], rax
	mov rdx, QWORD PTR [rdi]
	ror rdx, 11
	movabs rcx, 8725857424048159
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 59
	movabs rcx, 2296870857426870240
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 43
	movabs rcx, 57344
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 43
	movabs rcx, -2305596714850975744
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+80], rax
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 11
	movabs rcx, 8725857424048159
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 59
	movabs rcx, 2296870857426870240
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 43
	movabs rcx, 57344
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 43
	movabs rcx, -2305596714850975744
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+88], rax
	mov rdx, QWORD PTR [rdi]
	ror rdx, 34
	movabs rcx, 4128831
	and rdx, rcx
	mov rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 18
	movabs rcx, 70094935834560
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi]
	ror rdx, 2
	movabs rcx, 211109453807616
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 34
	movabs rcx, 17733194115710976
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 18
	movabs rcx, 4593671619917905920
	and rdx, rcx
	xor rax, rdx
	mov rdx, QWORD PTR [rdi+8]
	ror rdx, 2
	movabs rcx, -4611686018427387904
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rsi+96], rax
	ret
	.p2align 6

vg_idea_invert_key:
	mov r8, QWORD PTR [rdi+96]
	mov r9, r8
	mov ecx, 15
20:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 20b
	mov rdx, r9
	mov r10, rdx
	mov r11, QWORD PTR [rdi+96]
	shr r11, 16
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 16
	or r10, rdx
	mov r11, QWORD PTR [rdi+96]
	shr r11, 32
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 32
	or r10, rdx
	mov r8, QWORD PTR [rdi+96]
	shr r8, 48
	mov r9, r8
	mov ecx, 15
21:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 21b
	mov rdx, r9
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi], r10
	mov rdx, QWORD PTR [rdi+92]
	and rdx, 65535
	mov r10, rdx
	mov rdx, QWORD PTR [rdi+94]
	and rdx, 65535
	shl rdx, 16
	or r10, rdx
	mov r8, QWORD PTR [rdi+84]
	mov r9, r8
	mov ecx, 15
22:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 22b
	mov rdx, r9
	shl rdx, 32
	or r10, rdx
	mov r11, QWORD PTR [rdi+88]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+8], r10
	mov r11, QWORD PTR [rdi+86]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	mov r10, rdx
	mov r8, QWORD PTR [rdi+90]
	mov r9, r8
	mov ecx, 15
23:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 23b
	mov rdx, r9
	shl rdx, 16
	or r10, rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, 65535
	shl rdx, 32
	or r10, rdx
	mov rdx, QWORD PTR [rdi+82]
	and rdx, 65535
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+16], r10
	mov r8, QWORD PTR [rdi+72]
	mov r9, r8
	mov ecx, 15
24:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 24b
	mov rdx, r9
	mov r10, rdx
	mov r11, QWORD PTR [rdi+76]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 16
	or r10, rdx
	mov r11, QWORD PTR [rdi+74]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 32
	or r10, rdx
	mov r8, QWORD PTR [rdi+78]
	mov r9, r8
	mov ecx, 15
25:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 25b
	mov rdx, r9
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+24], r10
	mov rdx, QWORD PTR [rdi+68]
	and rdx, 65535
	mov r10, rdx
	mov rdx, QWORD PTR [rdi+70]
	and rdx, 65535
	shl rdx, 16
	or r10, rdx
	mov r8, QWORD PTR [rdi+60]
	mov r9, r8
	mov ecx, 15
26:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 26b
	mov rdx, r9
	shl rdx, 32
	or r10, rdx
	mov r11, QWORD PTR [rdi+64]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+32], r10
	mov r11, QWORD PTR [rdi+62]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	mov r10, rdx
	mov r8, QWORD PTR [rdi+66]
	mov r9, r8
	mov ecx, 15
27:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 27b
	mov rdx, r9
	shl rdx, 16
	or r10, rdx
	mov rdx, QWORD PTR [rdi+56]
	and rdx, 65535
	shl rdx, 32
	or r10, rdx
	mov rdx, QWORD PTR [rdi+58]
	and rdx, 65535
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+40], r10
	mov r8, QWORD PTR [rdi+48]
	mov r9, r8
	mov ecx, 15
28:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 28b
	mov rdx, r9
	mov r10, rdx
	mov r11, QWORD PTR [rdi+52]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 16
	or r10, rdx
	mov r11, QWORD PTR [rdi+50]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 32
	or r10, rdx
	mov r8, QWORD PTR [rdi+54]
	mov r9, r8
	mov ecx, 15
29:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 29b
	mov rdx, r9
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+48], r10
	mov rdx, QWORD PTR [rdi+44]
	and rdx, 65535
	mov r10, rdx
	mov rdx, QWORD PTR [rdi+46]
	and rdx, 65535
	shl rdx, 16
	or r10, rdx
	mov r8, QWORD PTR [rdi+36]
	mov r9, r8
	mov ecx, 15
210:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 210b
	mov rdx, r9
	shl rdx, 32
	or r10, rdx
	mov r11, QWORD PTR [rdi+40]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+56], r10
	mov r11, QWORD PTR [rdi+38]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	mov r10, rdx
	mov r8, QWORD PTR [rdi+42]
	mov r9, r8
	mov ecx, 15
211:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 211b
	mov rdx, r9
	shl rdx, 16
	or r10, rdx
	mov rdx, QWORD PTR [rdi+32]
	and rdx, 65535
	shl rdx, 32
	or r10, rdx
	mov rdx, QWORD PTR [rdi+34]
	and rdx, 65535
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+64], r10
	mov r8, QWORD PTR [rdi+24]
	mov r9, r8
	mov ecx, 15
212:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 212b
	mov rdx, r9
	mov r10, rdx
	mov r11, QWORD PTR [rdi+28]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 16
	or r10, rdx
	mov r11, QWORD PTR [rdi+26]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 32
	or r10, rdx
	mov r8, QWORD PTR [rdi+30]
	mov r9, r8
	mov ecx, 15
213:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 213b
	mov rdx, r9
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+72], r10
	mov rdx, QWORD PTR [rdi+20]
	and rdx, 65535
	mov r10, rdx
	mov rdx, QWORD PTR [rdi+22]
	and rdx, 65535
	shl rdx, 16
	or r10, rdx
	mov r8, QWORD PTR [rdi+12]
	mov r9, r8
	mov ecx, 15
214:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 214b
	mov rdx, r9
	shl rdx, 32
	or r10, rdx
	mov r11, QWORD PTR [rdi+16]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+80], r10
	mov r11, QWORD PTR [rdi+14]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	mov r10, rdx
	mov r8, QWORD PTR [rdi+18]
	mov r9, r8
	mov ecx, 15
215:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 215b
	mov rdx, r9
	shl rdx, 16
	or r10, rdx
	mov rdx, QWORD PTR [rdi+8]
	and rdx, 65535
	shl rdx, 32
	or r10, rdx
	mov rdx, QWORD PTR [rdi+10]
	and rdx, 65535
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+88], r10
	mov r8, QWORD PTR [rdi]
	mov r9, r8
	mov ecx, 15
216:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 216b
	mov rdx, r9
	mov r10, rdx
	mov r11, QWORD PTR [rdi+2]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 16
	or r10, rdx
	mov r11, QWORD PTR [rdi+4]
	mov edx, 0
	sub rdx, r11
	and rdx, 65535
	shl rdx, 32
	or r10, rdx
	mov r8, QWORD PTR [rdi+6]
	mov r9, r8
	mov ecx, 15
217:
	mov rax, r9
	mov rdx, r9
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
	mov rax, rdx
	mov rdx, r8
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
	mov r9, rdx
	sub rcx, 1
	jne 217b
	mov rdx, r9
	shl rdx, 48
	or r10, rdx
	mov QWORD PTR [rsi+96], r10
	ret
	.p2align 6

vg_idea_ecb:
	lea rsp, [rsp-24]
	mov rcx, rsp
	add rcx, 8
	test rdx, rdx
	je 20f
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov rbp, rdx
22:
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
	add rsi, 8
	sub rbp, 1
	jne 22b
	mov rbx, QWORD PTR [rcx]
	mov rbp, QWORD PTR [rcx+8]
	jmp 21f
20:
21:
	lea rsp, [rsp+24]
	ret
	.p2align 6
