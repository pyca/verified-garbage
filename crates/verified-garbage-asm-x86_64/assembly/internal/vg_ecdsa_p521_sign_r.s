// The functions of `src/internal/vg_ecdsa_p521_sign_r.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_sign_r:
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2584]
	add r8, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+4024], r8
	mov r8, QWORD PTR [rdi+2592]
	adc r8, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+2600]
	adc r8, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+2608]
	adc r8, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+2616]
	adc r8, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+2624]
	adc r8, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+2632]
	adc r8, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+2640]
	adc r8, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+2648]
	adc r8, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+2656], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+2664], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+2672], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+2680], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+2688], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+2696], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+2704], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+2712], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+2720], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2656]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2656], rdx
	mov rdx, QWORD PTR [rdi+2664]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2664], rdx
	mov rdx, QWORD PTR [rdi+2672]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2672], rdx
	mov rdx, QWORD PTR [rdi+2680]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2680], rdx
	mov rdx, QWORD PTR [rdi+2688]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2688], rdx
	mov rdx, QWORD PTR [rdi+2696]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2696], rdx
	mov rdx, QWORD PTR [rdi+2704]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2704], rdx
	mov rdx, QWORD PTR [rdi+2712]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2712], rdx
	mov rdx, QWORD PTR [rdi+2720]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2720], rdx
	mov r12, rsi
	mov esi, 2728
	mov edx, 2296
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+2368]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2376]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2384]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2392]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2400]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2408]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2416]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2424]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2432]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2368]
	or rdx, QWORD PTR [rdi+2376]
	or rdx, QWORD PTR [rdi+2384]
	or rdx, QWORD PTR [rdi+2392]
	or rdx, QWORD PTR [rdi+2400]
	or rdx, QWORD PTR [rdi+2408]
	or rdx, QWORD PTR [rdi+2416]
	or rdx, QWORD PTR [rdi+2424]
	or rdx, QWORD PTR [rdi+2432]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2296]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2304]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2312]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2320]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2328]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2336]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2344]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2352]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2360]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2296]
	or rdx, QWORD PTR [rdi+2304]
	or rdx, QWORD PTR [rdi+2312]
	or rdx, QWORD PTR [rdi+2320]
	or rdx, QWORD PTR [rdi+2328]
	or rdx, QWORD PTR [rdi+2336]
	or rdx, QWORD PTR [rdi+2344]
	or rdx, QWORD PTR [rdi+2352]
	or rdx, QWORD PTR [rdi+2360]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2656]
	or rdx, QWORD PTR [rdi+2664]
	or rdx, QWORD PTR [rdi+2672]
	or rdx, QWORD PTR [rdi+2680]
	or rdx, QWORD PTR [rdi+2688]
	or rdx, QWORD PTR [rdi+2696]
	or rdx, QWORD PTR [rdi+2704]
	or rdx, QWORD PTR [rdi+2712]
	or rdx, QWORD PTR [rdi+2720]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	ret
	.p2align 6
