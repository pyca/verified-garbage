// The functions of `src/brainpoolp512r1_mul.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_mul:
	movq xmm0, rbx
	movq xmm1, rbp
	movq xmm2, r12
	movq xmm3, r13
	movq xmm4, r14
	movq xmm5, r15
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2048]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2944], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2945], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2946], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2947], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2948], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2949], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2950], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2951], dl
	add rbx, 1
	cmp rbx, 64
	jne 20b
	mov rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+1920], rax
	mov rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+1928], rax
	mov rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+1936], rax
	mov rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+1944], rax
	mov rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+1952], rax
	mov rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1960], rax
	mov rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1968], rax
	mov rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1976], rax
	mov rax, QWORD PTR [rdi+1024]
	mov QWORD PTR [rdi+1984], rax
	mov rax, QWORD PTR [rdi+1032]
	mov QWORD PTR [rdi+1992], rax
	mov rax, QWORD PTR [rdi+1040]
	mov QWORD PTR [rdi+2000], rax
	mov rax, QWORD PTR [rdi+1048]
	mov QWORD PTR [rdi+2008], rax
	mov rax, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+2016], rax
	mov rax, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+2024], rax
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+2032], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+2040], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+1016], rax
	mov rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+1024], rax
	mov rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+1032], rax
	mov rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+1040], rax
	mov rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+1048], rax
	mov rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+1144], rax
	mov ebx, 512
21:
	sub rbx, 1
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+968]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+960]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+976]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+968]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+960]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+984]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+976]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+968]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+960]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+992]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+984]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+976]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+968]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+960]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1000]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+992]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+984]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+976]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+968]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+960]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1008]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1000]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+992]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+984]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+976]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+968]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+960]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1016]
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1008]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1000]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+992]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+984]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+976]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+968]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+960]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1016]
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1008]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1000]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+992]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+984]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+976]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+968]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1016]
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1008]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1000]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+992]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+984]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+976]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1016]
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1008]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1000]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+992]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+984]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1016]
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1008]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1000]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+992]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1016]
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1008]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1000]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1016]
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1008]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1016]
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1536], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1544], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1552], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1560], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1568], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1576], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1584], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1592], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1536]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1536], rdx
	mov rdx, QWORD PTR [rdi+1544]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1544], rdx
	mov rdx, QWORD PTR [rdi+1552]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1552], rdx
	mov rdx, QWORD PTR [rdi+1560]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1560], rdx
	mov rdx, QWORD PTR [rdi+1568]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1568], rdx
	mov rdx, QWORD PTR [rdi+1576]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1576], rdx
	mov rdx, QWORD PTR [rdi+1584]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1584], rdx
	mov rdx, QWORD PTR [rdi+1592]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1592], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1144]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1144]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1144]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1144]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1144]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1144]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1144]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1144]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1664], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1672], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1680], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1688], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1696], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1704], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1712], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1720], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1664]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1664], rdx
	mov rdx, QWORD PTR [rdi+1672]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1672], rdx
	mov rdx, QWORD PTR [rdi+1680]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1680], rdx
	mov rdx, QWORD PTR [rdi+1688]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1688], rdx
	mov rdx, QWORD PTR [rdi+1696]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1696], rdx
	mov rdx, QWORD PTR [rdi+1704]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, QWORD PTR [rdi+1712]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1712], rdx
	mov rdx, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1720], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+960]
	add r8, QWORD PTR [rdi+1024]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+968]
	adc r8, QWORD PTR [rdi+1032]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+976]
	adc r8, QWORD PTR [rdi+1040]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+984]
	adc r8, QWORD PTR [rdi+1048]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+992]
	adc r8, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1000]
	adc r8, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1008]
	adc r8, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1016]
	adc r8, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1728], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1736], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1744], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1752], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1760], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1768], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1776], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1784], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1728]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1728], rdx
	mov rdx, QWORD PTR [rdi+1736]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1736], rdx
	mov rdx, QWORD PTR [rdi+1744]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1744], rdx
	mov rdx, QWORD PTR [rdi+1752]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1752], rdx
	mov rdx, QWORD PTR [rdi+1760]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1760], rdx
	mov rdx, QWORD PTR [rdi+1768]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1768], rdx
	mov rdx, QWORD PTR [rdi+1776]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1776], rdx
	mov rdx, QWORD PTR [rdi+1784]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1784], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+960]
	add r8, QWORD PTR [rdi+1024]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+968]
	adc r8, QWORD PTR [rdi+1032]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+976]
	adc r8, QWORD PTR [rdi+1040]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+984]
	adc r8, QWORD PTR [rdi+1048]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+992]
	adc r8, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1000]
	adc r8, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1008]
	adc r8, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1016]
	adc r8, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1728], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1736], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1744], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1752], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1760], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1768], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1776], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1784], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1728]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1728], rdx
	mov rdx, QWORD PTR [rdi+1736]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1736], rdx
	mov rdx, QWORD PTR [rdi+1744]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1744], rdx
	mov rdx, QWORD PTR [rdi+1752]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1752], rdx
	mov rdx, QWORD PTR [rdi+1760]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1760], rdx
	mov rdx, QWORD PTR [rdi+1768]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1768], rdx
	mov rdx, QWORD PTR [rdi+1776]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1776], rdx
	mov rdx, QWORD PTR [rdi+1784]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1784], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1536]
	add r8, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1544]
	adc r8, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1552]
	adc r8, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1560]
	adc r8, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1568]
	adc r8, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1576]
	adc r8, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1584]
	adc r8, QWORD PTR [rdi+1648]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1592]
	adc r8, QWORD PTR [rdi+1656]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r8, QWORD PTR [rdi+1728]
	sub r8, QWORD PTR [rdi+1792]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1736]
	sbb r8, QWORD PTR [rdi+1800]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1744]
	sbb r8, QWORD PTR [rdi+1808]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1752]
	sbb r8, QWORD PTR [rdi+1816]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1760]
	sbb r8, QWORD PTR [rdi+1824]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1768]
	sbb r8, QWORD PTR [rdi+1832]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1776]
	sbb r8, QWORD PTR [rdi+1840]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1784]
	sbb r8, QWORD PTR [rdi+1848]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1728], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1736], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1744], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1752], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1760], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1768], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1776], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1784], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1728]
	mov QWORD PTR [rdi+1728], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1736]
	mov QWORD PTR [rdi+1736], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1744]
	mov QWORD PTR [rdi+1744], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1752]
	mov QWORD PTR [rdi+1752], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1760]
	mov QWORD PTR [rdi+1760], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1768]
	mov QWORD PTR [rdi+1768], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1776]
	mov QWORD PTR [rdi+1776], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1784], r8
	mov r9d, 0
	mov r8, QWORD PTR [rdi+960]
	add r8, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+968]
	adc r8, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+976]
	adc r8, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+984]
	adc r8, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+992]
	adc r8, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1000]
	adc r8, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1008]
	adc r8, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1016]
	adc r8, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+960]
	add r8, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+968]
	adc r8, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+976]
	adc r8, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+984]
	adc r8, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+992]
	adc r8, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1000]
	adc r8, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1008]
	adc r8, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1016]
	adc r8, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1536]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1544]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1552]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1560]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1568]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1576]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1584]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1592]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r8, QWORD PTR [rdi+1792]
	sub r8, QWORD PTR [rdi+1856]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1800]
	sbb r8, QWORD PTR [rdi+1864]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1808]
	sbb r8, QWORD PTR [rdi+1872]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1816]
	sbb r8, QWORD PTR [rdi+1880]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1824]
	sbb r8, QWORD PTR [rdi+1888]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1832]
	sbb r8, QWORD PTR [rdi+1896]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1840]
	sbb r8, QWORD PTR [rdi+1904]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1848]
	sbb r8, QWORD PTR [rdi+1912]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1848], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1792]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1800]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1808]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1816]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1824]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1832]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1840]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1848]
	mov QWORD PTR [rdi+1848], r8
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1024]
	add r8, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1032]
	adc r8, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1040]
	adc r8, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1048]
	adc r8, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1056]
	adc r8, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1064]
	adc r8, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1072]
	adc r8, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1080]
	adc r8, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1024]
	add r8, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1032]
	adc r8, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1040]
	adc r8, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1048]
	adc r8, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1056]
	adc r8, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1064]
	adc r8, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1072]
	adc r8, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1080]
	adc r8, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1208], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1152]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+1160]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+1168]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+1176]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+1184]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+1192]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+1200]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+1208]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1208], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1208], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1152]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+1160]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+1168]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+1176]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+1184]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+1192]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+1200]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+1208]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1208], rdx
	mov r8, QWORD PTR [rdi+1856]
	sub r8, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1864]
	sbb r8, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1872]
	sbb r8, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1880]
	sbb r8, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1888]
	sbb r8, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1896]
	sbb r8, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1904]
	sbb r8, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1912]
	sbb r8, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1912], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1856]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1864]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1872]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1880]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1888]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1896]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1904]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1912]
	mov QWORD PTR [rdi+1912], r8
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1280], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1288], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1296], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1304], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1312], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1320], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1328], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1336], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1280]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1280], rdx
	mov rdx, QWORD PTR [rdi+1288]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1288], rdx
	mov rdx, QWORD PTR [rdi+1296]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1296], rdx
	mov rdx, QWORD PTR [rdi+1304]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1304], rdx
	mov rdx, QWORD PTR [rdi+1312]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1312], rdx
	mov rdx, QWORD PTR [rdi+1320]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1320], rdx
	mov rdx, QWORD PTR [rdi+1328]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1328], rdx
	mov rdx, QWORD PTR [rdi+1336]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1336], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1208], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1152]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+1160]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+1168]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+1176]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+1184]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+1192]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+1200]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+1208]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1208], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1152]
	add r8, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1160]
	adc r8, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1168]
	adc r8, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1176]
	adc r8, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1184]
	adc r8, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1192]
	adc r8, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1200]
	adc r8, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1208]
	adc r8, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1280], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1288], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1296], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1304], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1312], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1320], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1328], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1336], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1280]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1280], rdx
	mov rdx, QWORD PTR [rdi+1288]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1288], rdx
	mov rdx, QWORD PTR [rdi+1296]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1296], rdx
	mov rdx, QWORD PTR [rdi+1304]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1304], rdx
	mov rdx, QWORD PTR [rdi+1312]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1312], rdx
	mov rdx, QWORD PTR [rdi+1320]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1320], rdx
	mov rdx, QWORD PTR [rdi+1328]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1328], rdx
	mov rdx, QWORD PTR [rdi+1336]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1336], rdx
	mov r8, QWORD PTR [rdi+1600]
	sub r8, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	sbb r8, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	sbb r8, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	sbb r8, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	sbb r8, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	sbb r8, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	sbb r8, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	sbb r8, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1208], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1208], r8
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1280], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1288], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1296], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1304], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1312], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1320], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1328], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1336], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1280]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1280], rdx
	mov rdx, QWORD PTR [rdi+1288]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1288], rdx
	mov rdx, QWORD PTR [rdi+1296]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1296], rdx
	mov rdx, QWORD PTR [rdi+1304]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1304], rdx
	mov rdx, QWORD PTR [rdi+1312]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1312], rdx
	mov rdx, QWORD PTR [rdi+1320]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1320], rdx
	mov rdx, QWORD PTR [rdi+1328]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1328], rdx
	mov rdx, QWORD PTR [rdi+1336]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1336], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1216], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1224], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1232], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1240], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1248], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1256], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1264], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1272], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1216]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1216], rdx
	mov rdx, QWORD PTR [rdi+1224]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1224], rdx
	mov rdx, QWORD PTR [rdi+1232]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1232], rdx
	mov rdx, QWORD PTR [rdi+1240]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1240], rdx
	mov rdx, QWORD PTR [rdi+1248]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1248], rdx
	mov rdx, QWORD PTR [rdi+1256]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1256], rdx
	mov rdx, QWORD PTR [rdi+1264]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1264], rdx
	mov rdx, QWORD PTR [rdi+1272]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1272], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1536]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1544]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1552]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1560]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1568]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1576]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1584]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1592]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1664], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1672], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1680], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1688], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1696], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1704], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1712], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1720], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1664]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1664], rdx
	mov rdx, QWORD PTR [rdi+1672]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1672], rdx
	mov rdx, QWORD PTR [rdi+1680]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1680], rdx
	mov rdx, QWORD PTR [rdi+1688]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1688], rdx
	mov rdx, QWORD PTR [rdi+1696]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1696], rdx
	mov rdx, QWORD PTR [rdi+1704]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, QWORD PTR [rdi+1712]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1712], rdx
	mov rdx, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1720], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r8, QWORD PTR [rdi+1536]
	sub r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1544]
	sbb r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1552]
	sbb r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1560]
	sbb r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1568]
	sbb r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1576]
	sbb r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1584]
	sbb r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1592]
	sbb r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1664], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1672], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1680], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1688], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1696], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1712], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1720], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+1664], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+1672], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+1680], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+1688], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+1696], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+1704], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+1712], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+1720], r8
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1664], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1672], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1680], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1688], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1696], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1704], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1712], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1720], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1664]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1664], rdx
	mov rdx, QWORD PTR [rdi+1672]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1672], rdx
	mov rdx, QWORD PTR [rdi+1680]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1680], rdx
	mov rdx, QWORD PTR [rdi+1688]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1688], rdx
	mov rdx, QWORD PTR [rdi+1696]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1696], rdx
	mov rdx, QWORD PTR [rdi+1704]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, QWORD PTR [rdi+1712]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1712], rdx
	mov rdx, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1720], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1792]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1800]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1808]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1816]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1824]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1832]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1840]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1848]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1536], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1544], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1552], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1560], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1568], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1576], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1584], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1592], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1536]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1536], rdx
	mov rdx, QWORD PTR [rdi+1544]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1544], rdx
	mov rdx, QWORD PTR [rdi+1552]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1552], rdx
	mov rdx, QWORD PTR [rdi+1560]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1560], rdx
	mov rdx, QWORD PTR [rdi+1568]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1568], rdx
	mov rdx, QWORD PTR [rdi+1576]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1576], rdx
	mov rdx, QWORD PTR [rdi+1584]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1584], rdx
	mov rdx, QWORD PTR [rdi+1592]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1592], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1216]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1224]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1232]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1240]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1248]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1256]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1264]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1272]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1216], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1224], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1232], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1240], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1248], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1256], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1264], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1272], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1216]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1216], rdx
	mov rdx, QWORD PTR [rdi+1224]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1224], rdx
	mov rdx, QWORD PTR [rdi+1232]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1232], rdx
	mov rdx, QWORD PTR [rdi+1240]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1240], rdx
	mov rdx, QWORD PTR [rdi+1248]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1248], rdx
	mov rdx, QWORD PTR [rdi+1256]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1256], rdx
	mov rdx, QWORD PTR [rdi+1264]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1264], rdx
	mov rdx, QWORD PTR [rdi+1272]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1272], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1536], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1544], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1552], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1560], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1568], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1576], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1584], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1592], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1536]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1536], rdx
	mov rdx, QWORD PTR [rdi+1544]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1544], rdx
	mov rdx, QWORD PTR [rdi+1552]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1552], rdx
	mov rdx, QWORD PTR [rdi+1560]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1560], rdx
	mov rdx, QWORD PTR [rdi+1568]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1568], rdx
	mov rdx, QWORD PTR [rdi+1576]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1576], rdx
	mov rdx, QWORD PTR [rdi+1584]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1584], rdx
	mov rdx, QWORD PTR [rdi+1592]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1592], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1208], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1152]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+1160]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+1168]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+1176]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+1184]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+1192]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+1200]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+1208]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1208], rdx
	mov r8, QWORD PTR [rdi+1152]
	sub r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1160]
	sbb r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1168]
	sbb r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1176]
	sbb r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1184]
	sbb r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1192]
	sbb r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1200]
	sbb r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1208]
	sbb r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1152], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1160], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1168], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1176], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1184], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1192], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1200], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1208], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+1152], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+1160], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+1168], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+1176], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+1184], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1192], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1200], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1208], r8
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1536], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1544], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1552], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1560], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1568], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1576], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1584], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1592], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1536]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1536], rdx
	mov rdx, QWORD PTR [rdi+1544]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1544], rdx
	mov rdx, QWORD PTR [rdi+1552]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1552], rdx
	mov rdx, QWORD PTR [rdi+1560]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1560], rdx
	mov rdx, QWORD PTR [rdi+1568]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1568], rdx
	mov rdx, QWORD PTR [rdi+1576]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1576], rdx
	mov rdx, QWORD PTR [rdi+1584]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1584], rdx
	mov rdx, QWORD PTR [rdi+1592]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1592], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1280], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1288], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1296], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1304], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1312], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1320], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1328], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1336], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1280]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1280], rdx
	mov rdx, QWORD PTR [rdi+1288]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1288], rdx
	mov rdx, QWORD PTR [rdi+1296]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1296], rdx
	mov rdx, QWORD PTR [rdi+1304]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1304], rdx
	mov rdx, QWORD PTR [rdi+1312]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1312], rdx
	mov rdx, QWORD PTR [rdi+1320]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1320], rdx
	mov rdx, QWORD PTR [rdi+1328]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1328], rdx
	mov rdx, QWORD PTR [rdi+1336]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1336], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1280]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1288]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1296]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1304]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1312]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1320]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1328]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1336]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1280], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1288], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1296], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1304], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1312], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1320], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1328], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1336], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1280]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1280], rdx
	mov rdx, QWORD PTR [rdi+1288]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1288], rdx
	mov rdx, QWORD PTR [rdi+1296]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1296], rdx
	mov rdx, QWORD PTR [rdi+1304]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1304], rdx
	mov rdx, QWORD PTR [rdi+1312]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1312], rdx
	mov rdx, QWORD PTR [rdi+1320]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1320], rdx
	mov rdx, QWORD PTR [rdi+1328]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1328], rdx
	mov rdx, QWORD PTR [rdi+1336]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1336], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1536], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1544], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1552], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1560], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1568], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1576], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1584], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1592], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1536]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1536], rdx
	mov rdx, QWORD PTR [rdi+1544]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1544], rdx
	mov rdx, QWORD PTR [rdi+1552]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1552], rdx
	mov rdx, QWORD PTR [rdi+1560]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1560], rdx
	mov rdx, QWORD PTR [rdi+1568]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1568], rdx
	mov rdx, QWORD PTR [rdi+1576]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1576], rdx
	mov rdx, QWORD PTR [rdi+1584]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1584], rdx
	mov rdx, QWORD PTR [rdi+1592]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1592], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1664], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1672], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1680], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1688], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1696], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1704], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1712], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1720], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1664]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1664], rdx
	mov rdx, QWORD PTR [rdi+1672]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1672], rdx
	mov rdx, QWORD PTR [rdi+1680]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1680], rdx
	mov rdx, QWORD PTR [rdi+1688]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1688], rdx
	mov rdx, QWORD PTR [rdi+1696]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1696], rdx
	mov rdx, QWORD PTR [rdi+1704]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, QWORD PTR [rdi+1712]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1712], rdx
	mov rdx, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1720], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1152]
	add r8, QWORD PTR [rdi+1216]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1160]
	adc r8, QWORD PTR [rdi+1224]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1168]
	adc r8, QWORD PTR [rdi+1232]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1176]
	adc r8, QWORD PTR [rdi+1240]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1184]
	adc r8, QWORD PTR [rdi+1248]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1192]
	adc r8, QWORD PTR [rdi+1256]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1200]
	adc r8, QWORD PTR [rdi+1264]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1208]
	adc r8, QWORD PTR [rdi+1272]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1728], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1736], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1744], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1752], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1760], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1768], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1776], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1784], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1728]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1728], rdx
	mov rdx, QWORD PTR [rdi+1736]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1736], rdx
	mov rdx, QWORD PTR [rdi+1744]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1744], rdx
	mov rdx, QWORD PTR [rdi+1752]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1752], rdx
	mov rdx, QWORD PTR [rdi+1760]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1760], rdx
	mov rdx, QWORD PTR [rdi+1768]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1768], rdx
	mov rdx, QWORD PTR [rdi+1776]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1776], rdx
	mov rdx, QWORD PTR [rdi+1784]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1784], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1920]
	add r8, QWORD PTR [rdi+1984]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1928]
	adc r8, QWORD PTR [rdi+1992]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1936]
	adc r8, QWORD PTR [rdi+2000]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1944]
	adc r8, QWORD PTR [rdi+2008]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1952]
	adc r8, QWORD PTR [rdi+2016]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1960]
	adc r8, QWORD PTR [rdi+2024]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1968]
	adc r8, QWORD PTR [rdi+2032]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1976]
	adc r8, QWORD PTR [rdi+2040]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1728], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1736], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1744], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1752], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1760], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1768], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1776], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1784], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1728]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1728], rdx
	mov rdx, QWORD PTR [rdi+1736]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1736], rdx
	mov rdx, QWORD PTR [rdi+1744]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1744], rdx
	mov rdx, QWORD PTR [rdi+1752]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1752], rdx
	mov rdx, QWORD PTR [rdi+1760]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1760], rdx
	mov rdx, QWORD PTR [rdi+1768]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1768], rdx
	mov rdx, QWORD PTR [rdi+1776]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1776], rdx
	mov rdx, QWORD PTR [rdi+1784]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1784], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1536]
	add r8, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1544]
	adc r8, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1552]
	adc r8, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1560]
	adc r8, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1568]
	adc r8, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1576]
	adc r8, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1584]
	adc r8, QWORD PTR [rdi+1648]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1592]
	adc r8, QWORD PTR [rdi+1656]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r8, QWORD PTR [rdi+1728]
	sub r8, QWORD PTR [rdi+1792]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1736]
	sbb r8, QWORD PTR [rdi+1800]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1744]
	sbb r8, QWORD PTR [rdi+1808]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1752]
	sbb r8, QWORD PTR [rdi+1816]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1760]
	sbb r8, QWORD PTR [rdi+1824]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1768]
	sbb r8, QWORD PTR [rdi+1832]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1776]
	sbb r8, QWORD PTR [rdi+1840]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1784]
	sbb r8, QWORD PTR [rdi+1848]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1728], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1736], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1744], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1752], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1760], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1768], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1776], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1784], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1728]
	mov QWORD PTR [rdi+1728], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1736]
	mov QWORD PTR [rdi+1736], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1744]
	mov QWORD PTR [rdi+1744], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1752]
	mov QWORD PTR [rdi+1752], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1760]
	mov QWORD PTR [rdi+1760], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1768]
	mov QWORD PTR [rdi+1768], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1776]
	mov QWORD PTR [rdi+1776], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1784]
	mov QWORD PTR [rdi+1784], r8
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1152]
	add r8, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1160]
	adc r8, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1168]
	adc r8, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1176]
	adc r8, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1184]
	adc r8, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1192]
	adc r8, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1200]
	adc r8, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1208]
	adc r8, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1920]
	add r8, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1928]
	adc r8, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1936]
	adc r8, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1944]
	adc r8, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1952]
	adc r8, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1960]
	adc r8, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1968]
	adc r8, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1976]
	adc r8, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1792]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1800]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1808]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1816]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1824]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1832]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov rax, QWORD PTR [rdi+1848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1536]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1544]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1552]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1560]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1568]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1576]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1584]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1592]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r8, QWORD PTR [rdi+1792]
	sub r8, QWORD PTR [rdi+1856]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1800]
	sbb r8, QWORD PTR [rdi+1864]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1808]
	sbb r8, QWORD PTR [rdi+1872]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1816]
	sbb r8, QWORD PTR [rdi+1880]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1824]
	sbb r8, QWORD PTR [rdi+1888]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1832]
	sbb r8, QWORD PTR [rdi+1896]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1840]
	sbb r8, QWORD PTR [rdi+1904]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1848]
	sbb r8, QWORD PTR [rdi+1912]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1848], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1792]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1800]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1808]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1816]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1824]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1832]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1840]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1848]
	mov QWORD PTR [rdi+1848], r8
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1216]
	add r8, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1224]
	adc r8, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1232]
	adc r8, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1240]
	adc r8, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1248]
	adc r8, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1256]
	adc r8, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1264]
	adc r8, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1272]
	adc r8, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1984]
	add r8, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1992]
	adc r8, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+2000]
	adc r8, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+2008]
	adc r8, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+2016]
	adc r8, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+2024]
	adc r8, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+2032]
	adc r8, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+2040]
	adc r8, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1344], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1352], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1360], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1368], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1376], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1384], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1392], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1400], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1344]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1344], rdx
	mov rdx, QWORD PTR [rdi+1352]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1352], rdx
	mov rdx, QWORD PTR [rdi+1360]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1360], rdx
	mov rdx, QWORD PTR [rdi+1368]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1368], rdx
	mov rdx, QWORD PTR [rdi+1376]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1376], rdx
	mov rdx, QWORD PTR [rdi+1384]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1384], rdx
	mov rdx, QWORD PTR [rdi+1392]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1392], rdx
	mov rdx, QWORD PTR [rdi+1400]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1400], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1912], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1344], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1352], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1360], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1368], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1376], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1384], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1392], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1400], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1344]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1344], rdx
	mov rdx, QWORD PTR [rdi+1352]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1352], rdx
	mov rdx, QWORD PTR [rdi+1360]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1360], rdx
	mov rdx, QWORD PTR [rdi+1368]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1368], rdx
	mov rdx, QWORD PTR [rdi+1376]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1376], rdx
	mov rdx, QWORD PTR [rdi+1384]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1384], rdx
	mov rdx, QWORD PTR [rdi+1392]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1392], rdx
	mov rdx, QWORD PTR [rdi+1400]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1400], rdx
	mov r8, QWORD PTR [rdi+1856]
	sub r8, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1864]
	sbb r8, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1872]
	sbb r8, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1880]
	sbb r8, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1888]
	sbb r8, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1896]
	sbb r8, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1904]
	sbb r8, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1912]
	sbb r8, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1856], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1912], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1856]
	mov QWORD PTR [rdi+1856], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1864]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1872]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1880]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1888]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1896]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1904]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1912]
	mov QWORD PTR [rdi+1912], r8
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1472], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1480], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1488], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1496], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1504], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1512], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1520], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1528], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1472]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1472], rdx
	mov rdx, QWORD PTR [rdi+1480]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1480], rdx
	mov rdx, QWORD PTR [rdi+1488]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1488], rdx
	mov rdx, QWORD PTR [rdi+1496]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1496], rdx
	mov rdx, QWORD PTR [rdi+1504]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1504], rdx
	mov rdx, QWORD PTR [rdi+1512]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1512], rdx
	mov rdx, QWORD PTR [rdi+1520]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1520], rdx
	mov rdx, QWORD PTR [rdi+1528]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1528], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1344], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1352], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1360], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1368], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1376], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1384], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1392], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1400], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1344]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1344], rdx
	mov rdx, QWORD PTR [rdi+1352]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1352], rdx
	mov rdx, QWORD PTR [rdi+1360]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1360], rdx
	mov rdx, QWORD PTR [rdi+1368]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1368], rdx
	mov rdx, QWORD PTR [rdi+1376]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1376], rdx
	mov rdx, QWORD PTR [rdi+1384]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1384], rdx
	mov rdx, QWORD PTR [rdi+1392]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1392], rdx
	mov rdx, QWORD PTR [rdi+1400]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1400], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1344]
	add r8, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1352]
	adc r8, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1360]
	adc r8, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1368]
	adc r8, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1376]
	adc r8, QWORD PTR [rdi+1504]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1384]
	adc r8, QWORD PTR [rdi+1512]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1392]
	adc r8, QWORD PTR [rdi+1520]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1400]
	adc r8, QWORD PTR [rdi+1528]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1472], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1480], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1488], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1496], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1504], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1512], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1520], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1528], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1472]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1472], rdx
	mov rdx, QWORD PTR [rdi+1480]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1480], rdx
	mov rdx, QWORD PTR [rdi+1488]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1488], rdx
	mov rdx, QWORD PTR [rdi+1496]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1496], rdx
	mov rdx, QWORD PTR [rdi+1504]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1504], rdx
	mov rdx, QWORD PTR [rdi+1512]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1512], rdx
	mov rdx, QWORD PTR [rdi+1520]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1520], rdx
	mov rdx, QWORD PTR [rdi+1528]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1528], rdx
	mov r8, QWORD PTR [rdi+1600]
	sub r8, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	sbb r8, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	sbb r8, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	sbb r8, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	sbb r8, QWORD PTR [rdi+1504]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	sbb r8, QWORD PTR [rdi+1512]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	sbb r8, QWORD PTR [rdi+1520]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	sbb r8, QWORD PTR [rdi+1528]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1344], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1352], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1360], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1368], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1376], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1384], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1392], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1400], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1344], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1352], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1360], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1368], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1376], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1384], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1392], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1400], r8
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1504]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1512]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1520]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1528]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1472], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1480], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1488], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1496], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1504], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1512], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1520], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1528], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1472]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1472], rdx
	mov rdx, QWORD PTR [rdi+1480]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1480], rdx
	mov rdx, QWORD PTR [rdi+1488]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1488], rdx
	mov rdx, QWORD PTR [rdi+1496]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1496], rdx
	mov rdx, QWORD PTR [rdi+1504]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1504], rdx
	mov rdx, QWORD PTR [rdi+1512]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1512], rdx
	mov rdx, QWORD PTR [rdi+1520]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1520], rdx
	mov rdx, QWORD PTR [rdi+1528]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1528], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1408], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1416], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1424], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1432], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1440], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1448], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1456], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1464], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1408]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1408], rdx
	mov rdx, QWORD PTR [rdi+1416]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1416], rdx
	mov rdx, QWORD PTR [rdi+1424]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1424], rdx
	mov rdx, QWORD PTR [rdi+1432]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1432], rdx
	mov rdx, QWORD PTR [rdi+1440]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1440], rdx
	mov rdx, QWORD PTR [rdi+1448]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1448], rdx
	mov rdx, QWORD PTR [rdi+1456]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1456], rdx
	mov rdx, QWORD PTR [rdi+1464]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1464], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1536]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1544]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1552]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1560]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1568]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1576]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1584]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1592]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1664], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1672], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1680], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1688], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1696], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1704], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1712], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1720], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1664]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1664], rdx
	mov rdx, QWORD PTR [rdi+1672]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1672], rdx
	mov rdx, QWORD PTR [rdi+1680]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1680], rdx
	mov rdx, QWORD PTR [rdi+1688]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1688], rdx
	mov rdx, QWORD PTR [rdi+1696]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1696], rdx
	mov rdx, QWORD PTR [rdi+1704]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, QWORD PTR [rdi+1712]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1712], rdx
	mov rdx, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1720], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1600]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1608]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1616]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1624]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1632]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1640]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1648]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1656]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1600], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1608], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1616], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1624], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1632], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1640], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1648], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1656], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1600]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1600], rdx
	mov rdx, QWORD PTR [rdi+1608]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1608], rdx
	mov rdx, QWORD PTR [rdi+1616]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1616], rdx
	mov rdx, QWORD PTR [rdi+1624]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1624], rdx
	mov rdx, QWORD PTR [rdi+1632]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1632], rdx
	mov rdx, QWORD PTR [rdi+1640]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1640], rdx
	mov rdx, QWORD PTR [rdi+1648]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1648], rdx
	mov rdx, QWORD PTR [rdi+1656]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1656], rdx
	mov r8, QWORD PTR [rdi+1536]
	sub r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1544]
	sbb r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1552]
	sbb r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1560]
	sbb r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1568]
	sbb r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1576]
	sbb r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1584]
	sbb r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1592]
	sbb r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1664], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1672], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1680], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1688], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1696], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1712], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1720], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+1664], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+1672], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+1680], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+1688], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+1696], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+1704], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+1712], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+1720], r8
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1664]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1672]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1680]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1688]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1664], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1672], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1680], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1688], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1696], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1704], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1712], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1720], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1664]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1664], rdx
	mov rdx, QWORD PTR [rdi+1672]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1672], rdx
	mov rdx, QWORD PTR [rdi+1680]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1680], rdx
	mov rdx, QWORD PTR [rdi+1688]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1688], rdx
	mov rdx, QWORD PTR [rdi+1696]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1696], rdx
	mov rdx, QWORD PTR [rdi+1704]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1704], rdx
	mov rdx, QWORD PTR [rdi+1712]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1712], rdx
	mov rdx, QWORD PTR [rdi+1720]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1720], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1792]
	add r8, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1800]
	adc r8, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1808]
	adc r8, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1816]
	adc r8, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1824]
	adc r8, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1832]
	adc r8, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1840]
	adc r8, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1848]
	adc r8, QWORD PTR [rdi+1720]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1600]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1608]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1616]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1624]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1632]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1640]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1648]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1656]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1536], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1544], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1552], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1560], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1568], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1576], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1584], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1592], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1536]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1536], rdx
	mov rdx, QWORD PTR [rdi+1544]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1544], rdx
	mov rdx, QWORD PTR [rdi+1552]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1552], rdx
	mov rdx, QWORD PTR [rdi+1560]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1560], rdx
	mov rdx, QWORD PTR [rdi+1568]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1568], rdx
	mov rdx, QWORD PTR [rdi+1576]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1576], rdx
	mov rdx, QWORD PTR [rdi+1584]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1584], rdx
	mov rdx, QWORD PTR [rdi+1592]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1592], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1408]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1416]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1424]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1432]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1440]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1448]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1456]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1464]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1408], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1416], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1424], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1432], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1440], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1448], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1456], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1464], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1408]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1408], rdx
	mov rdx, QWORD PTR [rdi+1416]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1416], rdx
	mov rdx, QWORD PTR [rdi+1424]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1424], rdx
	mov rdx, QWORD PTR [rdi+1432]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1432], rdx
	mov rdx, QWORD PTR [rdi+1440]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1440], rdx
	mov rdx, QWORD PTR [rdi+1448]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1448], rdx
	mov rdx, QWORD PTR [rdi+1456]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1456], rdx
	mov rdx, QWORD PTR [rdi+1464]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1464], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1792]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1800]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1808]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1816]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1824]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1832]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1536], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1544], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1552], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1560], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1568], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1576], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1584], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1592], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1536]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1536], rdx
	mov rdx, QWORD PTR [rdi+1544]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1544], rdx
	mov rdx, QWORD PTR [rdi+1552]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1552], rdx
	mov rdx, QWORD PTR [rdi+1560]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1560], rdx
	mov rdx, QWORD PTR [rdi+1568]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1568], rdx
	mov rdx, QWORD PTR [rdi+1576]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1576], rdx
	mov rdx, QWORD PTR [rdi+1584]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1584], rdx
	mov rdx, QWORD PTR [rdi+1592]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1592], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1344], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1352], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1360], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1368], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1376], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1384], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1392], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1400], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1344]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1344], rdx
	mov rdx, QWORD PTR [rdi+1352]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1352], rdx
	mov rdx, QWORD PTR [rdi+1360]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1360], rdx
	mov rdx, QWORD PTR [rdi+1368]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1368], rdx
	mov rdx, QWORD PTR [rdi+1376]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1376], rdx
	mov rdx, QWORD PTR [rdi+1384]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1384], rdx
	mov rdx, QWORD PTR [rdi+1392]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1392], rdx
	mov rdx, QWORD PTR [rdi+1400]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1400], rdx
	mov r8, QWORD PTR [rdi+1344]
	sub r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1352]
	sbb r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1360]
	sbb r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1368]
	sbb r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1376]
	sbb r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1384]
	sbb r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1392]
	sbb r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1400]
	sbb r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1344], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1352], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+1360], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+1368], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+1376], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+1384], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+1392], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+1400], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1344], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1352], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1360], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1368], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1376], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1384], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1392], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1400], r8
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1752]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1760]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1768]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1776]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1648]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1656]
	mov rax, QWORD PTR [rdi+1784]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1536], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1544], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1552], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1560], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1568], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1576], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1584], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1592], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1536]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1536], rdx
	mov rdx, QWORD PTR [rdi+1544]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1544], rdx
	mov rdx, QWORD PTR [rdi+1552]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1552], rdx
	mov rdx, QWORD PTR [rdi+1560]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1560], rdx
	mov rdx, QWORD PTR [rdi+1568]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1568], rdx
	mov rdx, QWORD PTR [rdi+1576]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1576], rdx
	mov rdx, QWORD PTR [rdi+1584]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1584], rdx
	mov rdx, QWORD PTR [rdi+1592]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1592], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1480]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1488]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1496]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1472], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1480], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1488], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1496], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1504], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1512], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1520], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1528], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1472]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1472], rdx
	mov rdx, QWORD PTR [rdi+1480]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1480], rdx
	mov rdx, QWORD PTR [rdi+1488]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1488], rdx
	mov rdx, QWORD PTR [rdi+1496]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1496], rdx
	mov rdx, QWORD PTR [rdi+1504]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1504], rdx
	mov rdx, QWORD PTR [rdi+1512]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1512], rdx
	mov rdx, QWORD PTR [rdi+1520]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1520], rdx
	mov rdx, QWORD PTR [rdi+1528]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1528], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+1472]
	add r8, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+1480]
	adc r8, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+1488]
	adc r8, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+1496]
	adc r8, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+1504]
	adc r8, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+1512]
	adc r8, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+1520]
	adc r8, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+1528]
	adc r8, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1472], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1480], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1488], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1496], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1504], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1512], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1520], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1528], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1472]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1472], rdx
	mov rdx, QWORD PTR [rdi+1480]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1480], rdx
	mov rdx, QWORD PTR [rdi+1488]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1488], rdx
	mov rdx, QWORD PTR [rdi+1496]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1496], rdx
	mov rdx, QWORD PTR [rdi+1504]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1504], rdx
	mov rdx, QWORD PTR [rdi+1512]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1512], rdx
	mov rdx, QWORD PTR [rdi+1520]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1520], rdx
	mov rdx, QWORD PTR [rdi+1528]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1528], rdx
	movzx eax, BYTE PTR [rdi+rbx*1+2944]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+1152]
	mov rdx, QWORD PTR [rdi+1344]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rdi+1160]
	mov rdx, QWORD PTR [rdi+1352]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rdi+1168]
	mov rdx, QWORD PTR [rdi+1360]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rdi+1176]
	mov rdx, QWORD PTR [rdi+1368]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rdi+1184]
	mov rdx, QWORD PTR [rdi+1376]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+1192]
	mov rdx, QWORD PTR [rdi+1384]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+1200]
	mov rdx, QWORD PTR [rdi+1392]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+1208]
	mov rdx, QWORD PTR [rdi+1400]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1016], rax
	mov rax, QWORD PTR [rdi+1216]
	mov rdx, QWORD PTR [rdi+1408]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1024], rax
	mov rax, QWORD PTR [rdi+1224]
	mov rdx, QWORD PTR [rdi+1416]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1032], rax
	mov rax, QWORD PTR [rdi+1232]
	mov rdx, QWORD PTR [rdi+1424]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1040], rax
	mov rax, QWORD PTR [rdi+1240]
	mov rdx, QWORD PTR [rdi+1432]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1048], rax
	mov rax, QWORD PTR [rdi+1248]
	mov rdx, QWORD PTR [rdi+1440]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+1256]
	mov rdx, QWORD PTR [rdi+1448]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+1264]
	mov rdx, QWORD PTR [rdi+1456]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1272]
	mov rdx, QWORD PTR [rdi+1464]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1280]
	mov rdx, QWORD PTR [rdi+1472]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1480]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1488]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1496]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1504]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1144], rax
	test rbx, rbx
	jne 21b
	movq rbx, xmm0
	movq rbp, xmm1
	movq r12, xmm2
	movq r13, xmm3
	movq r14, xmm4
	movq r15, xmm5
	ret
	.p2align 6
