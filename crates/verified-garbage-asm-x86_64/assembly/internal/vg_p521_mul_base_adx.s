// The functions of `src/internal/vg_p521_mul_base_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul_base_adx:
	mov QWORD PTR [rdi+2152], rbx
	mov QWORD PTR [rdi+2160], rbp
	mov QWORD PTR [rdi+2168], r12
	mov QWORD PTR [rdi+2176], r13
	mov QWORD PTR [rdi+2184], r14
	mov QWORD PTR [rdi+2192], r15
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2296]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3304], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3305], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3306], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3307], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3308], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3309], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3310], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3311], dl
	add rbx, 1
	cmp rbx, 72
	jne 20b
	movabs rax, -9217631144418712697
	mov QWORD PTR [rdi+2944], rax
	movabs rax, 8716614342792292383
	mov QWORD PTR [rdi+2952], rax
	movabs rax, -8963647668888889830
	mov QWORD PTR [rdi+2960], rax
	movabs rax, -4788688284897388321
	mov QWORD PTR [rdi+2968], rax
	movabs rax, -1104775416600182967
	mov QWORD PTR [rdi+2976], rax
	movabs rax, -442379411916359548
	mov QWORD PTR [rdi+2984], rax
	movabs rax, 8597773255975950730
	mov QWORD PTR [rdi+2992], rax
	movabs rax, 1137525115498218144
	mov QWORD PTR [rdi+3000], rax
	movabs rax, 77
	mov QWORD PTR [rdi+3008], rax
	movabs rax, -2911398454546468714
	mov QWORD PTR [rdi+1072], rax
	movabs rax, -2622805883304785837
	mov QWORD PTR [rdi+1080], rax
	movabs rax, -6758855595800436770
	mov QWORD PTR [rdi+1088], rax
	movabs rax, -3350014429734814130
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 9185203175476711091
	mov QWORD PTR [rdi+1104], rax
	movabs rax, -2793569313455226504
	mov QWORD PTR [rdi+1112], rax
	movabs rax, -9062608006907465467
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 3497699202216198480
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 458
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 5408250952697325544
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -267932407593670216
	mov QWORD PTR [rdi+1152], rax
	movabs rax, -8885807591840917390
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 8614545525818659092
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 4212919814057000474
	mov QWORD PTR [rdi+1176], rax
	movabs rax, -7381687526187518677
	mov QWORD PTR [rdi+1184], rax
	movabs rax, -4256878057158064348
	mov QWORD PTR [rdi+1192], rax
	movabs rax, -2260134842321433193
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 209
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	mov eax, 0
	mov QWORD PTR [rdi+3880], rax
	mov ebx, 83
21:
	sub rbx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3310]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3309]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3308]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3307]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3306]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3305]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3304]
	add rax, rdx
	sub rax, 64
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov rax, rbx
	mov ecx, 9216
	mul rcx
	lea rdx, {VG_P521_COMB}
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
	vpxor ymm3, ymm3, ymm3
	vpxor ymm4, ymm4, ymm4
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+112]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+144]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+176]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+208]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+240]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+400]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+432]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+464]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+496]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+528]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+688]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+720]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+752]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+784]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+816]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+976]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1008]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1040]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1072]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1104]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1264]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1296]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1328]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1360]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1392]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1552]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1584]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1616]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1648]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1680]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1840]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1872]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1904]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1936]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1968]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2128]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2160]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2192]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2224]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2256]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2416]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2448]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2480]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2512]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2544]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2560]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2592]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2624]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2656]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2688]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2704]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2736]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2768]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2800]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2832]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2848]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2880]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2912]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2944]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2976]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2992]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3024]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3056]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3088]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3120]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3136]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3168]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3200]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3232]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3264]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3280]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3312]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3344]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3376]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3408]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3424]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3456]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3488]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3520]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3552]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3568]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3600]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3632]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3664]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3696]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3712]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3744]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3776]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3808]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3840]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3856]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3888]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3920]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3952]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3984]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4000]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4032]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4064]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4096]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4128]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4144]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4176]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4208]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4240]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4272]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4288]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4352]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4384]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4416]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4432]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4464]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4496]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4528]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4560]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4576]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4608]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4640]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4672]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4704]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4720]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4752]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4784]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4816]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4848]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4864]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4896]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4928]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4960]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4992]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5008]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5040]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5072]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5104]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5136]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5152]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5184]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5216]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5248]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5280]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5296]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5328]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5360]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5392]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5424]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5440]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5472]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5504]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5536]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5568]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5584]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5616]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5648]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5680]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5712]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5728]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5760]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5792]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5824]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5856]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5872]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5904]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5936]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5968]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6000]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6016]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6048]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6080]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6112]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6144]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6160]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6192]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6224]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6256]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6288]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6304]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6336]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6368]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6400]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6432]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6448]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6480]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6512]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6544]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6576]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6592]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6624]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6656]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6688]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6720]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6736]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6768]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6800]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6832]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6864]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6880]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6912]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6944]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6976]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7008]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7024]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7056]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7088]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7120]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7152]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7168]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7200]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7232]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7264]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7296]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7312]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7344]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7376]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7408]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7440]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7456]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7488]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7520]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7552]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7584]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7600]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7632]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7664]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7696]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7728]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7744]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7776]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7808]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7840]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7872]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7888]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7952]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7984]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8016]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8032]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8064]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8096]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8128]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8160]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8176]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8208]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8240]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8272]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8304]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8320]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8352]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8384]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8416]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8448]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8464]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8496]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8528]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8560]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8592]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8608]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8640]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8672]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8704]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8736]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8752]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8784]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8816]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8848]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8880]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8896]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8928]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8960]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8992]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9024]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9040]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9072]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9104]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9136]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9168]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9184]
	vpor ymm4, ymm4, ymm11
	vmovdqu YMMWORD PTR [rdi+1504], ymm0
	vmovdqu YMMWORD PTR [rdi+1536], ymm1
	vmovdqu YMMWORD PTR [rdi+1568], ymm2
	vmovdqu YMMWORD PTR [rdi+1600], ymm3
	vmovdqu YMMWORD PTR [rdi+1616], ymm4
	vzeroupper
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 36028797018963968
	and rax, rcx
	or rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1576], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1584], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1592], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1600], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1608], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1616], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1624], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1632], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1640], rax
	xor rcx, -1
	movabs rax, 36028797018963968
	and rax, rcx
	mov QWORD PTR [rdi+1648], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1656], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1664], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1672], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1680], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1704], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1712], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2224
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+3310]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1576]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1584]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1592]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1600]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1608]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1616]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1624]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1632]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1640]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1640], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1072
	mov ecx, 1504
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1576
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 2008
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	mov r12, rsi
	mov esi, 2008
	mov edx, 1576
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 2008
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1360
	mov edx, 1504
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -288
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 288
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 2944
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 144
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1360
	mov edx, 2944
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 576
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 432
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	mov r12, rsi
	mov esi, 1792
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1360
	mov edx, 1288
	mov ecx, 1432
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1432
	mov edx, 2008
	mov ecx, 1432
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1936
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3310]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3309]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3308]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3307]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3306]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3305]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3304]
	add rax, rdx
	sub rax, 64
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov ecx, 0
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1072]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1080]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1088]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1096]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1104]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1112]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1120]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov rdx, QWORD PTR [rdi+1128]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov rdx, QWORD PTR [rdi+1136]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov rdx, QWORD PTR [rdi+1144]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov rdx, QWORD PTR [rdi+1152]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov rdx, QWORD PTR [rdi+1160]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov rdx, QWORD PTR [rdi+1168]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov rdx, QWORD PTR [rdi+1176]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov rdx, QWORD PTR [rdi+1184]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov rdx, QWORD PTR [rdi+1192]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov rdx, QWORD PTR [rdi+1200]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov rdx, QWORD PTR [rdi+1208]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov rdx, QWORD PTR [rdi+1224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov rdx, QWORD PTR [rdi+1232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1280], rax
	test rbx, rbx
	jne 21b
	mov rbx, QWORD PTR [rdi+2152]
	mov rbp, QWORD PTR [rdi+2160]
	mov r12, QWORD PTR [rdi+2168]
	mov r13, QWORD PTR [rdi+2176]
	mov r14, QWORD PTR [rdi+2184]
	mov r15, QWORD PTR [rdi+2192]
	ret
	.p2align 6
