// The functions of `src/internal/vg_p384_mul_base_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul_base_adx:
	mov QWORD PTR [rdi+1456], rbx
	mov QWORD PTR [rdi+1464], rbp
	mov QWORD PTR [rdi+1472], r12
	mov QWORD PTR [rdi+1480], r13
	mov QWORD PTR [rdi+1488], r14
	mov QWORD PTR [rdi+1496], r15
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1552]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2224], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2225], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2226], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2227], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2228], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2229], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2230], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2231], dl
	add rbx, 1
	cmp rbx, 48
	jne 20b
	movabs rax, 581395848458481100
	mov QWORD PTR [rdi+1984], rax
	movabs rax, -636786727019859220
	mov QWORD PTR [rdi+1992], rax
	movabs rax, 8643006485390950958
	mov QWORD PTR [rdi+2000], rax
	movabs rax, -2074105615313827102
	mov QWORD PTR [rdi+2008], rax
	movabs rax, -5320121202432139116
	mov QWORD PTR [rdi+2016], rax
	movabs rax, -3672666480684580871
	mov QWORD PTR [rdi+2024], rax
	mov eax, 0
	mov QWORD PTR [rdi+2608], rax
	mov ebx, 0
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2229]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2228]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2227]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2226]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2225]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2224]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	and r8, 128
	add rax, r8
	mov r8, rax
	mov rax, rbx
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vmovq xmm13, r8
	vpbroadcastd ymm13, xmm13
	mov ecx, 1
	vmovq xmm12, rcx
	vpbroadcastd ymm12, xmm12
	vmovdqa ymm14, ymm12
	vpxor ymm0, ymm0, ymm0
	vpxor ymm1, ymm1, ymm1
	vpxor ymm2, ymm2, ymm2
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+128]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+160]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+192]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+224]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+416]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+448]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+480]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+512]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+704]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+736]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+768]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+800]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+992]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1024]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1056]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1088]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1280]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1312]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1344]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1376]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1568]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1600]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1632]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1664]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1856]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1888]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1952]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2144]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2176]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2208]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2240]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2432]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2464]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2496]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2528]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2560]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2592]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2624]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2656]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2688]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2720]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2752]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2784]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2816]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2848]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2880]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2912]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2944]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2976]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3008]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3040]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3072]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3104]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3136]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3168]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3200]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3232]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3264]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3296]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3328]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3360]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3392]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3424]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3456]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3488]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3520]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3552]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3584]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3616]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3648]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3680]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3712]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3744]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3776]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3808]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3840]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3872]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3904]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3936]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3968]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4000]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4032]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4064]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4096]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4128]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4160]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4192]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4224]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4256]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4288]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4352]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4384]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4416]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4448]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4480]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4512]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4544]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4576]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4608]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4640]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4672]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4704]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4736]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4768]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4800]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4832]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4864]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4896]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4928]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4960]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4992]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5024]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5056]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5088]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5120]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5152]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5184]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5216]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5248]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5280]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5312]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5344]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5376]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5408]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5440]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5472]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5504]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5536]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5568]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5600]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5632]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5664]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5696]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5728]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5760]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5792]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5824]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5856]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5888]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5920]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5952]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5984]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6016]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6048]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6080]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6112]
	vpor ymm2, ymm2, ymm11
	vmovdqu YMMWORD PTR [rdi+1024], ymm0
	vmovdqu YMMWORD PTR [rdi+1056], ymm1
	vmovdqu YMMWORD PTR [rdi+1088], ymm2
	vzeroupper
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, -4294967295
	and rax, rcx
	or rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 4294967295
	and rax, rcx
	or rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1112], rax
	xor rcx, -1
	movabs rax, -4294967295
	and rax, rcx
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 4294967295
	and rax, rcx
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 1
	and rax, rcx
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1160], rax
	mov r8, QWORD PTR [rdi+208]
	mov r9, QWORD PTR [rdi+216]
	mov r10, QWORD PTR [rdi+224]
	mov r11, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+240]
	mov r13, QWORD PTR [rdi+248]
	sub r8, QWORD PTR [rdi+1072]
	sbb r9, QWORD PTR [rdi+1080]
	sbb r10, QWORD PTR [rdi+1088]
	sbb r11, QWORD PTR [rdi+1096]
	sbb r12, QWORD PTR [rdi+1104]
	sbb r13, QWORD PTR [rdi+1112]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1504], r8
	mov QWORD PTR [rdi+1512], r9
	mov QWORD PTR [rdi+1520], r10
	mov QWORD PTR [rdi+1528], r11
	mov QWORD PTR [rdi+1536], r12
	mov QWORD PTR [rdi+1544], r13
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2230]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+1072]
	mov rdx, QWORD PTR [rdi+1504]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1080]
	mov rdx, QWORD PTR [rdi+1512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1088]
	mov rdx, QWORD PTR [rdi+1520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1096]
	mov rdx, QWORD PTR [rdi+1528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1104]
	mov rdx, QWORD PTR [rdi+1536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1112]
	mov rdx, QWORD PTR [rdi+1544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1024]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+1032]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+1040]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+1048]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+872], rax
	mov ebx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2229]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2228]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2227]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2226]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2225]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2224]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2223]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	and r8, 128
	add rax, r8
	mov r8, rax
	mov rax, rbx
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vmovq xmm13, r8
	vpbroadcastd ymm13, xmm13
	mov ecx, 1
	vmovq xmm12, rcx
	vpbroadcastd ymm12, xmm12
	vmovdqa ymm14, ymm12
	vpxor ymm0, ymm0, ymm0
	vpxor ymm1, ymm1, ymm1
	vpxor ymm2, ymm2, ymm2
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+128]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+160]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+192]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+224]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+416]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+448]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+480]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+512]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+704]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+736]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+768]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+800]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+992]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1024]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1056]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1088]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1280]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1312]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1344]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1376]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1568]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1600]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1632]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1664]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1856]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1888]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1952]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2144]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2176]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2208]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2240]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2432]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2464]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2496]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2528]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2560]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2592]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2624]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2656]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2688]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2720]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2752]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2784]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2816]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2848]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2880]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2912]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2944]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2976]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3008]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3040]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3072]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3104]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3136]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3168]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3200]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3232]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3264]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3296]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3328]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3360]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3392]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3424]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3456]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3488]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3520]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3552]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3584]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3616]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3648]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3680]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3712]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3744]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3776]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3808]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3840]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3872]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3904]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3936]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3968]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4000]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4032]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4064]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4096]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4128]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4160]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4192]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4224]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4256]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4288]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4352]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4384]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4416]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4448]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4480]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4512]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4544]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4576]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4608]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4640]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4672]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4704]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4736]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4768]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4800]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4832]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4864]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4896]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4928]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4960]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4992]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5024]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5056]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5088]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5120]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5152]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5184]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5216]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5248]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5280]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5312]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5344]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5376]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5408]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5440]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5472]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5504]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5536]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5568]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5600]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5632]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5664]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5696]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5728]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5760]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5792]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5824]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5856]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5888]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5920]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5952]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5984]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6016]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6048]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6080]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6112]
	vpor ymm2, ymm2, ymm11
	vmovdqu YMMWORD PTR [rdi+1024], ymm0
	vmovdqu YMMWORD PTR [rdi+1056], ymm1
	vmovdqu YMMWORD PTR [rdi+1088], ymm2
	vzeroupper
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, -4294967295
	and rax, rcx
	or rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 4294967295
	and rax, rcx
	or rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1112], rax
	xor rcx, -1
	movabs rax, -4294967295
	and rax, rcx
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 4294967295
	and rax, rcx
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 1
	and rax, rcx
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1160], rax
	mov r8, QWORD PTR [rdi+208]
	mov r9, QWORD PTR [rdi+216]
	mov r10, QWORD PTR [rdi+224]
	mov r11, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+240]
	mov r13, QWORD PTR [rdi+248]
	sub r8, QWORD PTR [rdi+1072]
	sbb r9, QWORD PTR [rdi+1080]
	sbb r10, QWORD PTR [rdi+1088]
	sbb r11, QWORD PTR [rdi+1096]
	sbb r12, QWORD PTR [rdi+1104]
	sbb r13, QWORD PTR [rdi+1112]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1504], r8
	mov QWORD PTR [rdi+1512], r9
	mov QWORD PTR [rdi+1520], r10
	mov QWORD PTR [rdi+1528], r11
	mov QWORD PTR [rdi+1536], r12
	mov QWORD PTR [rdi+1544], r13
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2230]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+1072]
	mov rdx, QWORD PTR [rdi+1504]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1080]
	mov rdx, QWORD PTR [rdi+1512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1088]
	mov rdx, QWORD PTR [rdi+1520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1096]
	mov rdx, QWORD PTR [rdi+1528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1104]
	mov rdx, QWORD PTR [rdi+1536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1112]
	mov rdx, QWORD PTR [rdi+1544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
21:
	add rbx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2229]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2228]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2227]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2226]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2225]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2224]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2223]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	and r8, 128
	add rax, r8
	mov r8, rax
	sub rbx, 1
	vmovq xmm13, r8
	vpbroadcastd ymm13, xmm13
	mov ecx, 1
	vmovq xmm12, rcx
	vpbroadcastd ymm12, xmm12
	vmovdqa ymm14, ymm12
	vpxor ymm0, ymm0, ymm0
	vpxor ymm1, ymm1, ymm1
	vpxor ymm2, ymm2, ymm2
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+840]
	mulx r10, rax, QWORD PTR [rdi+848]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+856]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+864]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+872]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+872]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+872]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+872]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+872]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+864]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+872]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+128]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+160]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+192]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+224]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+1024]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1168]
	mulx r10, rax, QWORD PTR [rdi+1176]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1184]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1192]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1200]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1208]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1032]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1040]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1048]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1056]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1064]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1216], r14
	mov QWORD PTR [rdi+1224], r15
	mov QWORD PTR [rdi+1232], r8
	mov QWORD PTR [rdi+1240], r9
	mov QWORD PTR [rdi+1248], r10
	mov QWORD PTR [rdi+1256], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+416]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+448]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+480]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+512]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1168]
	mulx r10, rax, QWORD PTR [rdi+1176]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1184]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1192]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1200]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1208]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+704]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+736]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+768]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+800]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+1072]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1264]
	mulx r10, rax, QWORD PTR [rdi+1272]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1280]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1288]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1296]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1304]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1080]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1088]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1096]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1112]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+992]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1024]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1056]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1088]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1280]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1312]
	vpor ymm2, ymm2, ymm11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1344]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1376]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1568]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1600]
	vpor ymm2, ymm2, ymm11
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	sub r8, QWORD PTR [rdi+784]
	sbb r9, QWORD PTR [rdi+792]
	sbb r10, QWORD PTR [rdi+800]
	sbb r11, QWORD PTR [rdi+808]
	sbb r12, QWORD PTR [rdi+816]
	sbb r13, QWORD PTR [rdi+824]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1632]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1664]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1856]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1888]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1952]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1224]
	mulx r10, rax, QWORD PTR [rdi+1232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1248]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1256]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1224]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1256]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1248]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1216]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1224]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1232]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1240]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1248]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1256]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1312], r13
	mov QWORD PTR [rdi+1320], r14
	mov QWORD PTR [rdi+1328], r15
	mov QWORD PTR [rdi+1336], r8
	mov QWORD PTR [rdi+1344], r9
	mov QWORD PTR [rdi+1352], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1312]
	adc r14, QWORD PTR [rdi+1320]
	adc r15, QWORD PTR [rdi+1328]
	adc r10, QWORD PTR [rdi+1336]
	adc r11, QWORD PTR [rdi+1344]
	adc r12, QWORD PTR [rdi+1352]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1312], r13
	mov QWORD PTR [rdi+1320], r14
	mov QWORD PTR [rdi+1328], r15
	mov QWORD PTR [rdi+1336], r10
	mov QWORD PTR [rdi+1344], r11
	mov QWORD PTR [rdi+1352], r12
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2144]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2176]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2208]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2240]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1344]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1352]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1224]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1248]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1256]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2432]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2464]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2496]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2528]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2560]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2592]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2624]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2656]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1344]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1352]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+760]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+768]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+776]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2688]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2720]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2752]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2784]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2816]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2848]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2880]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2912]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2944]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2976]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3008]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3040]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+1264]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1272]
	mulx r10, rax, QWORD PTR [rdi+1280]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1288]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1296]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1304]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1304]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1264]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1272]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1280]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1288]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1296]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1304]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+880], r13
	mov QWORD PTR [rdi+888], r14
	mov QWORD PTR [rdi+896], r15
	mov QWORD PTR [rdi+904], r8
	mov QWORD PTR [rdi+912], r9
	mov QWORD PTR [rdi+920], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+880]
	adc r14, QWORD PTR [rdi+888]
	adc r15, QWORD PTR [rdi+896]
	adc r10, QWORD PTR [rdi+904]
	adc r11, QWORD PTR [rdi+912]
	adc r12, QWORD PTR [rdi+920]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+880], r13
	mov QWORD PTR [rdi+888], r14
	mov QWORD PTR [rdi+896], r15
	mov QWORD PTR [rdi+904], r10
	mov QWORD PTR [rdi+912], r11
	mov QWORD PTR [rdi+920], r12
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3072]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3104]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3136]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3168]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3200]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3232]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3264]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3296]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3328]
	vpor ymm2, ymm2, ymm11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+1360]
	sbb r9, QWORD PTR [rdi+1368]
	sbb r10, QWORD PTR [rdi+1376]
	sbb r11, QWORD PTR [rdi+1384]
	sbb r12, QWORD PTR [rdi+1392]
	sbb r13, QWORD PTR [rdi+1400]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3360]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3392]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3424]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3456]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3488]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3520]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3552]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3584]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3616]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3648]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3680]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3712]
	vpor ymm2, ymm2, ymm11
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1312]
	adc r9, QWORD PTR [rdi+1320]
	adc r10, QWORD PTR [rdi+1328]
	adc r11, QWORD PTR [rdi+1336]
	adc r12, QWORD PTR [rdi+1344]
	adc r13, QWORD PTR [rdi+1352]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3744]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3776]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3808]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3840]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3872]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3904]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3936]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3968]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4000]
	vpor ymm2, ymm2, ymm11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+1408]
	sbb r9, QWORD PTR [rdi+1416]
	sbb r10, QWORD PTR [rdi+1424]
	sbb r11, QWORD PTR [rdi+1432]
	sbb r12, QWORD PTR [rdi+1440]
	sbb r13, QWORD PTR [rdi+1448]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4032]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4064]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4096]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4128]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4160]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4192]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4224]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4256]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4288]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4352]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4384]
	vpor ymm2, ymm2, ymm11
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+880]
	sbb r9, QWORD PTR [rdi+888]
	sbb r10, QWORD PTR [rdi+896]
	sbb r11, QWORD PTR [rdi+904]
	sbb r12, QWORD PTR [rdi+912]
	sbb r13, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4416]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4448]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4480]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4512]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4544]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4576]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4608]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4640]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4672]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+1264]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1344]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1352]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1304]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4704]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4736]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4768]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4800]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4832]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4864]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4896]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4928]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4960]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4992]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5024]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5056]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+784]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1360]
	mulx r10, rax, QWORD PTR [rdi+1368]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1376]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1384]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1392]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1400]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+792]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+800]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+808]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+816]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+824]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5088]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5120]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5152]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5184]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5216]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5248]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5280]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5312]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5344]
	vpor ymm2, ymm2, ymm11
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+1360]
	sbb r9, QWORD PTR [rdi+1368]
	sbb r10, QWORD PTR [rdi+1376]
	sbb r11, QWORD PTR [rdi+1384]
	sbb r12, QWORD PTR [rdi+1392]
	sbb r13, QWORD PTR [rdi+1400]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5376]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5408]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5440]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5472]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5504]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5536]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5568]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5600]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5632]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5664]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5696]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5728]
	vpor ymm2, ymm2, ymm11
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1216]
	mulx r10, rax, QWORD PTR [rdi+1224]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1232]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1240]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1248]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1256]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_P384_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5760]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5792]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5824]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5856]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5888]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5920]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5952]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5984]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6016]
	vpor ymm2, ymm2, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6048]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6080]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6112]
	vpor ymm2, ymm2, ymm11
	mov rax, QWORD PTR [rdi+832]
	or rax, QWORD PTR [rdi+840]
	or rax, QWORD PTR [rdi+848]
	or rax, QWORD PTR [rdi+856]
	or rax, QWORD PTR [rdi+864]
	or rax, QWORD PTR [rdi+872]
	mov ecx, 0
	sub rcx, rax
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+1024]
	mov rdx, QWORD PTR [rdi+880]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rdi+1032]
	mov rdx, QWORD PTR [rdi+888]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rdi+1040]
	mov rdx, QWORD PTR [rdi+896]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rdi+1048]
	mov rdx, QWORD PTR [rdi+904]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rdi+1056]
	mov rdx, QWORD PTR [rdi+912]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rdi+1064]
	mov rdx, QWORD PTR [rdi+920]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rdi+1072]
	mov rdx, QWORD PTR [rdi+928]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rdi+1080]
	mov rdx, QWORD PTR [rdi+936]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rdi+1088]
	mov rdx, QWORD PTR [rdi+944]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rdi+1096]
	mov rdx, QWORD PTR [rdi+952]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rdi+1104]
	mov rdx, QWORD PTR [rdi+960]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rdi+1112]
	mov rdx, QWORD PTR [rdi+968]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rdi+1120]
	mov rdx, QWORD PTR [rdi+976]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rdi+1128]
	mov rdx, QWORD PTR [rdi+984]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rdi+1136]
	mov rdx, QWORD PTR [rdi+992]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+1144]
	mov rdx, QWORD PTR [rdi+1000]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+1152]
	mov rdx, QWORD PTR [rdi+1008]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+1160]
	mov rdx, QWORD PTR [rdi+1016]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1016], rax
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2229]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2228]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2227]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2226]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2225]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2224]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2223]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	and r8, 128
	add rax, r8
	mov r8, rax
	mov ecx, 0
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+880]
	mov rdx, QWORD PTR [rdi+736]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+888]
	mov rdx, QWORD PTR [rdi+744]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+896]
	mov rdx, QWORD PTR [rdi+752]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+904]
	mov rdx, QWORD PTR [rdi+760]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+912]
	mov rdx, QWORD PTR [rdi+768]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rdi+920]
	mov rdx, QWORD PTR [rdi+776]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rdi+928]
	mov rdx, QWORD PTR [rdi+784]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+936]
	mov rdx, QWORD PTR [rdi+792]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+944]
	mov rdx, QWORD PTR [rdi+800]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+952]
	mov rdx, QWORD PTR [rdi+808]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+960]
	mov rdx, QWORD PTR [rdi+816]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+968]
	mov rdx, QWORD PTR [rdi+824]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rdi+976]
	mov rdx, QWORD PTR [rdi+832]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rdi+984]
	mov rdx, QWORD PTR [rdi+840]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rdi+992]
	mov rdx, QWORD PTR [rdi+848]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rdi+1000]
	mov rdx, QWORD PTR [rdi+856]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rdi+1008]
	mov rdx, QWORD PTR [rdi+864]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rdi+1016]
	mov rdx, QWORD PTR [rdi+872]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+872], rax
	add rbx, 1
	vmovdqu YMMWORD PTR [rdi+1024], ymm0
	vmovdqu YMMWORD PTR [rdi+1056], ymm1
	vmovdqu YMMWORD PTR [rdi+1088], ymm2
	vzeroupper
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2229]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2228]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2227]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2226]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2225]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2224]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2223]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	and r8, 128
	add rax, r8
	mov r8, rax
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, -4294967295
	and rax, rcx
	or rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 4294967295
	and rax, rcx
	or rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1112], rax
	xor rcx, -1
	movabs rax, -4294967295
	and rax, rcx
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 4294967295
	and rax, rcx
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 1
	and rax, rcx
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1160], rax
	mov r8, QWORD PTR [rdi+208]
	mov r9, QWORD PTR [rdi+216]
	mov r10, QWORD PTR [rdi+224]
	mov r11, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+240]
	mov r13, QWORD PTR [rdi+248]
	sub r8, QWORD PTR [rdi+1072]
	sbb r9, QWORD PTR [rdi+1080]
	sbb r10, QWORD PTR [rdi+1088]
	sbb r11, QWORD PTR [rdi+1096]
	sbb r12, QWORD PTR [rdi+1104]
	sbb r13, QWORD PTR [rdi+1112]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1504], r8
	mov QWORD PTR [rdi+1512], r9
	mov QWORD PTR [rdi+1520], r10
	mov QWORD PTR [rdi+1528], r11
	mov QWORD PTR [rdi+1536], r12
	mov QWORD PTR [rdi+1544], r13
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2230]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+1072]
	mov rdx, QWORD PTR [rdi+1504]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1080]
	mov rdx, QWORD PTR [rdi+1512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1088]
	mov rdx, QWORD PTR [rdi+1520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1096]
	mov rdx, QWORD PTR [rdi+1528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1104]
	mov rdx, QWORD PTR [rdi+1536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1112]
	mov rdx, QWORD PTR [rdi+1544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	cmp rbx, 54
	jne 21b
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+840]
	mulx r10, rax, QWORD PTR [rdi+848]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+856]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+864]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+872]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+872]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+872]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+872]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+872]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+864]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+872]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov rdx, QWORD PTR [rdi+1024]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1168]
	mulx r10, rax, QWORD PTR [rdi+1176]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1184]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1192]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1200]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1208]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1032]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1040]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1048]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1056]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1064]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1216], r14
	mov QWORD PTR [rdi+1224], r15
	mov QWORD PTR [rdi+1232], r8
	mov QWORD PTR [rdi+1240], r9
	mov QWORD PTR [rdi+1248], r10
	mov QWORD PTR [rdi+1256], r11
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1168]
	mulx r10, rax, QWORD PTR [rdi+1176]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1184]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1192]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1200]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1208]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov rdx, QWORD PTR [rdi+1072]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1264]
	mulx r10, rax, QWORD PTR [rdi+1272]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1280]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1288]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1296]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1304]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1080]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1088]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1096]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1112]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	sub r8, QWORD PTR [rdi+784]
	sbb r9, QWORD PTR [rdi+792]
	sbb r10, QWORD PTR [rdi+800]
	sbb r11, QWORD PTR [rdi+808]
	sbb r12, QWORD PTR [rdi+816]
	sbb r13, QWORD PTR [rdi+824]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1224]
	mulx r10, rax, QWORD PTR [rdi+1232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1248]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1256]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1224]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1256]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1248]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1216]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1224]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1232]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1240]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1248]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1256]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1312], r13
	mov QWORD PTR [rdi+1320], r14
	mov QWORD PTR [rdi+1328], r15
	mov QWORD PTR [rdi+1336], r8
	mov QWORD PTR [rdi+1344], r9
	mov QWORD PTR [rdi+1352], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1312]
	adc r14, QWORD PTR [rdi+1320]
	adc r15, QWORD PTR [rdi+1328]
	adc r10, QWORD PTR [rdi+1336]
	adc r11, QWORD PTR [rdi+1344]
	adc r12, QWORD PTR [rdi+1352]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1312], r13
	mov QWORD PTR [rdi+1320], r14
	mov QWORD PTR [rdi+1328], r15
	mov QWORD PTR [rdi+1336], r10
	mov QWORD PTR [rdi+1344], r11
	mov QWORD PTR [rdi+1352], r12
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1344]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1352]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1224]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1248]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1256]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1344]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1352]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+760]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+768]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+776]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov rdx, QWORD PTR [rdi+1264]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1272]
	mulx r10, rax, QWORD PTR [rdi+1280]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1288]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1296]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1304]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1304]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1264]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1272]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1280]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1288]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1296]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1304]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+880], r13
	mov QWORD PTR [rdi+888], r14
	mov QWORD PTR [rdi+896], r15
	mov QWORD PTR [rdi+904], r8
	mov QWORD PTR [rdi+912], r9
	mov QWORD PTR [rdi+920], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+880]
	adc r14, QWORD PTR [rdi+888]
	adc r15, QWORD PTR [rdi+896]
	adc r10, QWORD PTR [rdi+904]
	adc r11, QWORD PTR [rdi+912]
	adc r12, QWORD PTR [rdi+920]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+880], r13
	mov QWORD PTR [rdi+888], r14
	mov QWORD PTR [rdi+896], r15
	mov QWORD PTR [rdi+904], r10
	mov QWORD PTR [rdi+912], r11
	mov QWORD PTR [rdi+920], r12
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+1360]
	sbb r9, QWORD PTR [rdi+1368]
	sbb r10, QWORD PTR [rdi+1376]
	sbb r11, QWORD PTR [rdi+1384]
	sbb r12, QWORD PTR [rdi+1392]
	sbb r13, QWORD PTR [rdi+1400]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1312]
	adc r9, QWORD PTR [rdi+1320]
	adc r10, QWORD PTR [rdi+1328]
	adc r11, QWORD PTR [rdi+1336]
	adc r12, QWORD PTR [rdi+1344]
	adc r13, QWORD PTR [rdi+1352]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+1408]
	sbb r9, QWORD PTR [rdi+1416]
	sbb r10, QWORD PTR [rdi+1424]
	sbb r11, QWORD PTR [rdi+1432]
	sbb r12, QWORD PTR [rdi+1440]
	sbb r13, QWORD PTR [rdi+1448]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+880]
	sbb r9, QWORD PTR [rdi+888]
	sbb r10, QWORD PTR [rdi+896]
	sbb r11, QWORD PTR [rdi+904]
	sbb r12, QWORD PTR [rdi+912]
	sbb r13, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov rdx, QWORD PTR [rdi+1264]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1344]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1352]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1304]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov rdx, QWORD PTR [rdi+784]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1360]
	mulx r10, rax, QWORD PTR [rdi+1368]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1376]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1384]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1392]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1400]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+792]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+800]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+808]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+816]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+824]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+1360]
	sbb r9, QWORD PTR [rdi+1368]
	sbb r10, QWORD PTR [rdi+1376]
	sbb r11, QWORD PTR [rdi+1384]
	sbb r12, QWORD PTR [rdi+1392]
	sbb r13, QWORD PTR [rdi+1400]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1216]
	mulx r10, rax, QWORD PTR [rdi+1224]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1232]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1240]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1248]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1256]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov rax, QWORD PTR [rdi+832]
	or rax, QWORD PTR [rdi+840]
	or rax, QWORD PTR [rdi+848]
	or rax, QWORD PTR [rdi+856]
	or rax, QWORD PTR [rdi+864]
	or rax, QWORD PTR [rdi+872]
	mov ecx, 0
	sub rcx, rax
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+1024]
	mov rdx, QWORD PTR [rdi+880]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rdi+1032]
	mov rdx, QWORD PTR [rdi+888]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rdi+1040]
	mov rdx, QWORD PTR [rdi+896]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rdi+1048]
	mov rdx, QWORD PTR [rdi+904]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rdi+1056]
	mov rdx, QWORD PTR [rdi+912]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rdi+1064]
	mov rdx, QWORD PTR [rdi+920]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rdi+1072]
	mov rdx, QWORD PTR [rdi+928]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rdi+1080]
	mov rdx, QWORD PTR [rdi+936]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rdi+1088]
	mov rdx, QWORD PTR [rdi+944]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rdi+1096]
	mov rdx, QWORD PTR [rdi+952]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rdi+1104]
	mov rdx, QWORD PTR [rdi+960]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rdi+1112]
	mov rdx, QWORD PTR [rdi+968]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rdi+1120]
	mov rdx, QWORD PTR [rdi+976]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rdi+1128]
	mov rdx, QWORD PTR [rdi+984]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rdi+1136]
	mov rdx, QWORD PTR [rdi+992]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+1144]
	mov rdx, QWORD PTR [rdi+1000]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+1152]
	mov rdx, QWORD PTR [rdi+1008]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+1160]
	mov rdx, QWORD PTR [rdi+1016]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1016], rax
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2229]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2228]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2227]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2226]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2225]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2224]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2223]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	and r8, 128
	add rax, r8
	mov r8, rax
	mov ecx, 0
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+880]
	mov rdx, QWORD PTR [rdi+736]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+888]
	mov rdx, QWORD PTR [rdi+744]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+896]
	mov rdx, QWORD PTR [rdi+752]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+904]
	mov rdx, QWORD PTR [rdi+760]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+912]
	mov rdx, QWORD PTR [rdi+768]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rdi+920]
	mov rdx, QWORD PTR [rdi+776]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rdi+928]
	mov rdx, QWORD PTR [rdi+784]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+936]
	mov rdx, QWORD PTR [rdi+792]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+944]
	mov rdx, QWORD PTR [rdi+800]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+952]
	mov rdx, QWORD PTR [rdi+808]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+960]
	mov rdx, QWORD PTR [rdi+816]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+968]
	mov rdx, QWORD PTR [rdi+824]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rdi+976]
	mov rdx, QWORD PTR [rdi+832]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rdi+984]
	mov rdx, QWORD PTR [rdi+840]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rdi+992]
	mov rdx, QWORD PTR [rdi+848]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rdi+1000]
	mov rdx, QWORD PTR [rdi+856]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rdi+1008]
	mov rdx, QWORD PTR [rdi+864]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rdi+1016]
	mov rdx, QWORD PTR [rdi+872]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+872], rax
	add rbx, 1
	cmp rbx, 55
	mov rax, QWORD PTR [rdi+832]
	or rax, QWORD PTR [rdi+840]
	or rax, QWORD PTR [rdi+848]
	or rax, QWORD PTR [rdi+856]
	or rax, QWORD PTR [rdi+864]
	or rax, QWORD PTR [rdi+872]
	mov ecx, 0
	sub rcx, rax
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+784]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+216]
	mov rdx, QWORD PTR [rdi+792]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+224]
	mov rdx, QWORD PTR [rdi+800]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+232]
	mov rdx, QWORD PTR [rdi+808]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+240]
	mov rdx, QWORD PTR [rdi+816]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+248]
	mov rdx, QWORD PTR [rdi+824]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+824], rax
	xor rcx, -1
	movabs rax, -4294967295
	and rax, rcx
	or rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	movabs rax, 4294967295
	and rax, rcx
	or rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+864]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+872]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+760]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+768]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+776]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+736], r14
	mov QWORD PTR [rdi+744], r15
	mov QWORD PTR [rdi+752], r8
	mov QWORD PTR [rdi+760], r9
	mov QWORD PTR [rdi+768], r10
	mov QWORD PTR [rdi+776], r11
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+840]
	mulx r10, rax, QWORD PTR [rdi+848]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+856]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+864]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+872]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+872]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+872]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+872]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+872]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+864]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+872]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov rdx, QWORD PTR [rdi+1168]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+864]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+872]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1176]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1184]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1192]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1200]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1208]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+832], r14
	mov QWORD PTR [rdi+840], r15
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov QWORD PTR [rdi+864], r10
	mov QWORD PTR [rdi+872], r11
	mov rbx, QWORD PTR [rdi+1456]
	mov rbp, QWORD PTR [rdi+1464]
	mov r12, QWORD PTR [rdi+1472]
	mov r13, QWORD PTR [rdi+1480]
	mov r14, QWORD PTR [rdi+1488]
	mov r15, QWORD PTR [rdi+1496]
	ret
	.p2align 6
