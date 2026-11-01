// The functions of `src/internal/vg_p256_mul_base_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_mul_base_adx:
	mov QWORD PTR [rdi+992], rbx
	mov QWORD PTR [rdi+1000], rbp
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov QWORD PTR [rdi+1376], r14
	mov QWORD PTR [rdi+1384], r15
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1056]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1504], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1505], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1506], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1507], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1508], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1509], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1510], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1511], dl
	add rbx, 1
	cmp rbx, 32
	jne 20b
	movabs rax, -2838148052449706529
	mov QWORD PTR [rdi+1344], rax
	movabs rax, -5985277524727025520
	mov QWORD PTR [rdi+1352], rax
	movabs rax, -1899920169839284522
	mov QWORD PTR [rdi+1360], rax
	movabs rax, -2580555864783501260
	mov QWORD PTR [rdi+1368], rax
	mov eax, 0
	mov QWORD PTR [rdi+1760], rax
	mov ebx, 0
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1509]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1508]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1507]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1506]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1505]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1504]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	and r8, 128
	add rax, r8
	mov r8, rax
	mov rax, rbx
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vmovq xmm13, r8
	vpbroadcastd ymm13, xmm13
	mov ecx, 1
	vmovq xmm12, rcx
	vpbroadcastd ymm12, xmm12
	vmovdqa ymm14, ymm12
	vpxor ymm0, ymm0, ymm0
	vpxor ymm1, ymm1, ymm1
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+128]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+160]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+192]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+224]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+416]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+448]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+480]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+512]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+704]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+736]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+768]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+800]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+992]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1024]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1056]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1088]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1280]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1312]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1344]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1376]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1568]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1600]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1632]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1664]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1856]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1888]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1952]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2144]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2176]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2208]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2240]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2432]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2464]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2496]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2528]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2560]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2592]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2624]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2656]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2688]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2720]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2752]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2784]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2816]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2848]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2880]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2912]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2944]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2976]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3008]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3040]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3072]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3104]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3136]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3168]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3200]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3232]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3264]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3296]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3328]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3360]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3392]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3424]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3456]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3488]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3520]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3552]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3584]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3616]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3648]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3680]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3712]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3744]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3776]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3808]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3840]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3872]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3904]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3936]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3968]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4000]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4032]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4064]
	vpor ymm1, ymm1, ymm11
	vmovdqu YMMWORD PTR [rdi+704], ymm0
	vmovdqu YMMWORD PTR [rdi+736], ymm1
	vzeroupper
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	movabs rax, -4294967296
	and rax, rcx
	or rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	movabs rax, -1
	and rax, rcx
	or rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	movabs rax, 4294967294
	and rax, rcx
	or rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	xor rcx, -1
	movabs rax, 1
	and rax, rcx
	mov QWORD PTR [rdi+768], rax
	movabs rax, -4294967296
	and rax, rcx
	mov QWORD PTR [rdi+776], rax
	movabs rax, -1
	and rax, rcx
	mov QWORD PTR [rdi+784], rax
	movabs rax, 4294967294
	and rax, rcx
	mov QWORD PTR [rdi+792], rax
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+1510]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+736]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+744]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+752]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+760]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+600], rax
	mov ebx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1509]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1508]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1507]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1506]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1505]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1504]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1503]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	and r8, 128
	add rax, r8
	mov r8, rax
	mov rax, rbx
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vmovq xmm13, r8
	vpbroadcastd ymm13, xmm13
	mov ecx, 1
	vmovq xmm12, rcx
	vpbroadcastd ymm12, xmm12
	vmovdqa ymm14, ymm12
	vpxor ymm0, ymm0, ymm0
	vpxor ymm1, ymm1, ymm1
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+128]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+160]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+192]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+224]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+416]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+448]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+480]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+512]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+704]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+736]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+768]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+800]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+992]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1024]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1056]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1088]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1280]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1312]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1344]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1376]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1568]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1600]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1632]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1664]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1856]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1888]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1952]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2144]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2176]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2208]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2240]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2432]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2464]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2496]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2528]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2560]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2592]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2624]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2656]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2688]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2720]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2752]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2784]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2816]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2848]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2880]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2912]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2944]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2976]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3008]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3040]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3072]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3104]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3136]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3168]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3200]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3232]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3264]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3296]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3328]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3360]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3392]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3424]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3456]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3488]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3520]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3552]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3584]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3616]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3648]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3680]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3712]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3744]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3776]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3808]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3840]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3872]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3904]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3936]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3968]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4000]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4032]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4064]
	vpor ymm1, ymm1, ymm11
	vmovdqu YMMWORD PTR [rdi+704], ymm0
	vmovdqu YMMWORD PTR [rdi+736], ymm1
	vzeroupper
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	movabs rax, -4294967296
	and rax, rcx
	or rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	movabs rax, -1
	and rax, rcx
	or rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	movabs rax, 4294967294
	and rax, rcx
	or rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	xor rcx, -1
	movabs rax, 1
	and rax, rcx
	mov QWORD PTR [rdi+768], rax
	movabs rax, -4294967296
	and rax, rcx
	mov QWORD PTR [rdi+776], rax
	movabs rax, -1
	and rax, rcx
	mov QWORD PTR [rdi+784], rax
	movabs rax, 4294967294
	and rax, rcx
	mov QWORD PTR [rdi+792], rax
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+1510]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+736]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+744]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+752]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+760]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+760], rax
21:
	add rbx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1509]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1508]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1507]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1506]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1505]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1504]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1503]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
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
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+128]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+160]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+824]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+728]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+824]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+192]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+224]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+416]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+824]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+600]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+824]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+448]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+480]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+512]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+864]
	mulx r10, rax, QWORD PTR [rdi+872]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+880]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+888]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+888]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+888]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+760]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+888]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+704]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+736]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+768]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+800]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm1, ymm1, ymm11
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+992]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1024]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1056]
	vpor ymm1, ymm1, ymm11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+544]
	sbb r9, QWORD PTR [rdi+552]
	sbb r10, QWORD PTR [rdi+560]
	sbb r11, QWORD PTR [rdi+568]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1088]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1280]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1312]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+856]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1344]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1376]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov QWORD PTR [rdi+952], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1568]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1600]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1632]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1664]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1856]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1888]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1952]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+872]
	mulx r11, rax, QWORD PTR [rdi+880]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+888]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+888]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+880]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+888]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+864]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+872]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+880]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+888]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov QWORD PTR [rdi+632], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2144]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2176]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2208]
	vpor ymm1, ymm1, ymm11
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2240]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2432]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2464]
	vpor ymm1, ymm1, ymm11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12d, 0
	add r8, QWORD PTR [rdi+896]
	adc r9, QWORD PTR [rdi+904]
	adc r10, QWORD PTR [rdi+912]
	adc r11, QWORD PTR [rdi+920]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2496]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2528]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2560]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2592]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2624]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2656]
	vpor ymm1, ymm1, ymm11
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+960]
	sbb r9, QWORD PTR [rdi+968]
	sbb r10, QWORD PTR [rdi+976]
	sbb r11, QWORD PTR [rdi+984]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2688]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2720]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2752]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2784]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2816]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2848]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2880]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2912]
	vpor ymm1, ymm1, ymm11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+608]
	sbb r9, QWORD PTR [rdi+616]
	sbb r10, QWORD PTR [rdi+624]
	sbb r11, QWORD PTR [rdi+632]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2944]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2976]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3008]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3040]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3072]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3104]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+880]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+888]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3136]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3168]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3200]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3232]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3264]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3296]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3328]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3360]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+928]
	mulx r10, rax, QWORD PTR [rdi+936]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+952]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+952]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov QWORD PTR [rdi+952], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3392]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3424]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3456]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3488]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3520]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3552]
	vpor ymm1, ymm1, ymm11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3584]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3616]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3648]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3680]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3712]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3744]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3776]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3808]
	vpor ymm1, ymm1, ymm11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
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
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
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
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+600]
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
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	mov QWORD PTR [rdi+696], r15
	mov rax, rbx
	add rax, 1
	mov ecx, 4096
	mul rcx
	lea rdx, {VG_P256_COMB}
	add rdx, rax
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3840]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3872]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3904]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3936]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3968]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4000]
	vpor ymm1, ymm1, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4032]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4064]
	vpor ymm1, ymm1, ymm11
	mov rax, QWORD PTR [rdi+576]
	or rax, QWORD PTR [rdi+584]
	or rax, QWORD PTR [rdi+592]
	or rax, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rax
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+704]
	mov rdx, QWORD PTR [rdi+608]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rdi+712]
	mov rdx, QWORD PTR [rdi+616]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rdi+720]
	mov rdx, QWORD PTR [rdi+624]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rdi+728]
	mov rdx, QWORD PTR [rdi+632]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rdi+736]
	mov rdx, QWORD PTR [rdi+640]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rdi+744]
	mov rdx, QWORD PTR [rdi+648]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rdi+752]
	mov rdx, QWORD PTR [rdi+656]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rdi+760]
	mov rdx, QWORD PTR [rdi+664]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rdi+768]
	mov rdx, QWORD PTR [rdi+672]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rdi+776]
	mov rdx, QWORD PTR [rdi+680]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rdi+784]
	mov rdx, QWORD PTR [rdi+688]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rdi+792]
	mov rdx, QWORD PTR [rdi+696]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+696], rax
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1509]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1508]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1507]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1506]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1505]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1504]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1503]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
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
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rdi+632]
	mov rdx, QWORD PTR [rdi+536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+552]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+560]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+568]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+576]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+584]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+592]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rdi+696]
	mov rdx, QWORD PTR [rdi+600]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+600], rax
	add rbx, 1
	vmovdqu YMMWORD PTR [rdi+704], ymm0
	vmovdqu YMMWORD PTR [rdi+736], ymm1
	vzeroupper
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1509]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1508]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1507]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1506]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1505]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1504]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1503]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
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
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	movabs rax, -4294967296
	and rax, rcx
	or rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	movabs rax, -1
	and rax, rcx
	or rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	movabs rax, 4294967294
	and rax, rcx
	or rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	xor rcx, -1
	movabs rax, 1
	and rax, rcx
	mov QWORD PTR [rdi+768], rax
	movabs rax, -4294967296
	and rax, rcx
	mov QWORD PTR [rdi+776], rax
	movabs rax, -1
	and rax, rcx
	mov QWORD PTR [rdi+784], rax
	movabs rax, 4294967294
	and rax, rcx
	mov QWORD PTR [rdi+792], rax
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+1510]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+736]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+744]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+752]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+760]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+760], rax
	cmp rbx, 36
	jne 21b
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, QWORD PTR [rdi+704]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+712]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+720]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+824]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+728]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+824]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+824]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+600]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+824]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+864]
	mulx r10, rax, QWORD PTR [rdi+872]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+880]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+888]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+888]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+888]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+760]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+888]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+544]
	sbb r9, QWORD PTR [rdi+552]
	sbb r10, QWORD PTR [rdi+560]
	sbb r11, QWORD PTR [rdi+568]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+856]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov QWORD PTR [rdi+952], r15
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+872]
	mulx r11, rax, QWORD PTR [rdi+880]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+888]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+888]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+880]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+888]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+864]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+872]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+880]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+888]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov QWORD PTR [rdi+632], r15
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12d, 0
	add r8, QWORD PTR [rdi+896]
	adc r9, QWORD PTR [rdi+904]
	adc r10, QWORD PTR [rdi+912]
	adc r11, QWORD PTR [rdi+920]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+960]
	sbb r9, QWORD PTR [rdi+968]
	sbb r10, QWORD PTR [rdi+976]
	sbb r11, QWORD PTR [rdi+984]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+608], r8
	mov QWORD PTR [rdi+616], r9
	mov QWORD PTR [rdi+624], r10
	mov QWORD PTR [rdi+632], r11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+608]
	sbb r9, QWORD PTR [rdi+616]
	sbb r10, QWORD PTR [rdi+624]
	sbb r11, QWORD PTR [rdi+632]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+880]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+888]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+928]
	mulx r10, rax, QWORD PTR [rdi+936]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+952]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+952]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov QWORD PTR [rdi+952], r15
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
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
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
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
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+600]
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
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	mov QWORD PTR [rdi+696], r15
	mov rax, QWORD PTR [rdi+576]
	or rax, QWORD PTR [rdi+584]
	or rax, QWORD PTR [rdi+592]
	or rax, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rax
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+704]
	mov rdx, QWORD PTR [rdi+608]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rdi+712]
	mov rdx, QWORD PTR [rdi+616]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rdi+720]
	mov rdx, QWORD PTR [rdi+624]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rdi+728]
	mov rdx, QWORD PTR [rdi+632]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rdi+736]
	mov rdx, QWORD PTR [rdi+640]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rdi+744]
	mov rdx, QWORD PTR [rdi+648]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rdi+752]
	mov rdx, QWORD PTR [rdi+656]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rdi+760]
	mov rdx, QWORD PTR [rdi+664]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rdi+768]
	mov rdx, QWORD PTR [rdi+672]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rdi+776]
	mov rdx, QWORD PTR [rdi+680]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rdi+784]
	mov rdx, QWORD PTR [rdi+688]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rdi+792]
	mov rdx, QWORD PTR [rdi+696]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+696], rax
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1509]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1508]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1507]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1506]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1505]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+1504]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1503]
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rcx*1+1510]
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
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rdi+632]
	mov rdx, QWORD PTR [rdi+536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+552]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+560]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+568]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+576]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+584]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+592]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rdi+696]
	mov rdx, QWORD PTR [rdi+600]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+600], rax
	add rbx, 1
	cmp rbx, 37
	mov rax, QWORD PTR [rdi+576]
	or rax, QWORD PTR [rdi+584]
	or rax, QWORD PTR [rdi+592]
	or rax, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rax
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+552]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+560]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+568]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+568], rax
	xor rcx, -1
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	movabs rax, -4294967296
	and rax, rcx
	or rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	movabs rax, -1
	and rax, rcx
	or rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	movabs rax, 4294967294
	and rax, rcx
	or rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r14
	mov QWORD PTR [rdi+536], r15
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, QWORD PTR [rdi+800]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+808]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+816]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+824]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	mov rbx, QWORD PTR [rdi+992]
	mov rbp, QWORD PTR [rdi+1000]
	mov r12, QWORD PTR [rdi+1008]
	mov r13, QWORD PTR [rdi+1016]
	mov r14, QWORD PTR [rdi+1376]
	mov r15, QWORD PTR [rdi+1384]
	ret
	.p2align 6
